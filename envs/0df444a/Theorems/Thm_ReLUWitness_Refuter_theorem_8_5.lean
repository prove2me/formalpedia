-- Prove2me | Theorems.Thm_ReLUWitness_Refuter_theorem_8_5
-- name    : ReLUWitness.Refuter.theorem_8_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:55:47.906843+00:00
-- url     : https://prove2.me/theorems/ce2101d3-8c3e-408c-b78a-6ad1aa0fbbc6
-- title:
--   Theorem 8.5 — for each fixed prime q and depth K, VTC⁰ proves an FTC⁰ refuter for ReLU depth K on more than q^K inputs
-- statement:
--   Fix externally a prime $q$ and an integer $K\ge1$, and a polynomial $p_0$ with nonnegative integer coefficients for which Lemma A.2 holds; put $p(m)=p_0(m)+2^{100}(m+2)^{40}$. Work in the two-sorted theory $\mathbf{VTC}^0$ and its conservative extension $T$ by chosen $\mathrm{FTC}^0$ function symbols. Networks are coded by the exact record $N$ of §2.3 (scalar rational ReLU networks, unreduced rational weights and arbitrary rational biases). $\mathrm{Net}(N,n)$ is complete validity with input dimension $n$, and the depth is the number of hidden layers. $\mathrm{ValGood}_q(N,n)$ says that every nonbias entry normalizes without failure under the normalization graphs of Lemma 8.4, which repeatedly cancel common factors $q$. $\mathrm{Err}_K(N,n,x)$ says that $x$ is a valid rational $n$-vector at which the guarded fixed-depth evaluator $\mathrm{Eval}_K$ returns a value different from $\mathrm{MAX}_n(x)$.
--
--   **Theorem 8.5.** There is a total chosen $\mathrm{FTC}^0$ function $A^{TC}_{q,K}$ such that $T$ proves
--
--   $$\forall n\,\forall N\,\Big(\mathrm{Net}(N,n)\wedge n\ge q^K+1\wedge \mathrm{depth}(N)\le K\wedge\mathrm{ValGood}_q(N,n)\ \to\ |A^{TC}_{q,K}(n,N)|\le p(|N|)\ \wedge\ \mathrm{Err}_K\big(N,n,A^{TC}_{q,K}(n,N)\big)\Big).$$
--
--   In the standard model this says that a network with nonbias denominators free of $q$ after cancellation cannot compute $\max(x_1,\dots,x_n)$ with $K$ hidden layers once $n>q^K$, and that a disagreement point is found by a threshold circuit of polynomial size and constant depth. The theorem adds that the refuter's correctness is provable in the weak theory $\mathbf{VTC}^0$, with one cutoff $p$ for all $q$ and $K$. The polynomial bounding the refuter's auxiliary arrays may depend on $q$ and $K$.
--
--   **Formalization Note.** $q$, $K$ and $p_0$ are meta-level parameters (one theorem per triple). "A total chosen $\mathrm{FTC}^0$ function" is a symbol $F_k$ of a well-formed program $P$ of chosen definitions, with one number argument $n$ and one string argument $N$. "$T$ proves" is truth in every model of $T(P)$. The predicates are those of the definition items, read in the model, and $q^K+1$ and $K$ are numerals.
--
--   Differences from the source:
--   - encoding: VTC⁰ proves the guarantee in its conservative definitional extension T → the guarantee holds in every two-sorted model of T(P): 2-BASIC, Σ^B_0 comprehension for the language of P, the counting axiom, the defining axioms of the primitives and of P; reason: completeness theorem; T proves every axiom of T(P) (Fact 8.1, [CN10, Theorem 9.34(c)]), so the Lean statement implies the paper's
--   - encoding: the imported FTC⁰ functions (counting, iterated addition, multiplication, iterated multiplication IMUL with interval products, division DIV, subtraction) and the AC⁰ helpers (rows, cut, shift, signed recoding) → primitive symbols axiomatized by their bit-definitions and the recurrence equations Fact 2.3 and Fact 8.1 import; reason: these are FTC⁰ functions of T satisfying exactly these T-provable equations
--   - encoding: a total chosen FTC⁰ function → a symbol of a well-formed program of Σ^B_0 bit-definitions and bounded minimizations over the primitives (signature: one number, one string argument, string value); reason: FTC⁰ is the AC⁰ closure of the counting function [CN10]; each such definition is total and comes with its defining graph
--   - encoding: the bounded formulas Net, ValGood_q, Eval_K, Err_K, MAX_n, p(|N|) → their meaning in an arbitrary model, with auxiliary exact arrays as existential string witnesses given by their exact bits; reason: Σ^B_0 comprehension provides them and extensionality makes them unique, so this is the paper's formula
--   - reading: MAX_n(x) under cross-product comparison → the first maximal coordinate of x (cross-product order); reason: the selection convention of p. 47; all maximal coordinates have the same value
--   - reading: ValGood_q evaluated by the normalization graphs of Lemma 8.4 → the final flag f_m = [ν_u < ν_v ∧ m > ν_u] computed from ν_u, ν_v (greatest t ≤ m with q^t dividing the magnitude, via IMUL and DIV) at every weight entry, after Net; reason: this is the graph defined in the proof of Lemma 8.4 (pp. 50-51)
--   - reading: p₀ supplied by Lemma A.2 → any p₀ ∈ ℕ[X] satisfying the conclusion of Lemma A.2 (hypothesis hp₀); reason: p. 21 fixes p₀ as a polynomial supplied by Lemma A.2
-- source:
--   Myrisiotis, A Witnessing Duality for ReLU Network Depth, arXiv:2610.38281v1, p. 52, Theorem 8.5 (= Theorem 1.1, p. 4)

import Mathlib
import Definitions.Def_ReLUWitness_Refuter_VTC0
import Definitions.Def_ReLUWitness_Refuter_Standard

namespace ReLUWitness.Refuter

/-- Theorem 8.5 (a threshold-computable refuter). For every prime `q`, every `K ≥ 1` and every
polynomial `p₀` with nonnegative integer coefficients satisfying Lemma A.2, there is a chosen
FTC⁰ function symbol `A(n, N)` (definition `k` of a well-formed program `P`) such that the
extension `T(P)` of VTC⁰ proves: for every valid network code `N` with input dimension
`n ≥ q^K + 1`, hidden depth at most `K` and `ValGood_q(N,n)`, the output `A(n,N)` has length
at most `p(|N|) = p₀(|N|) + 2^100 (|N|+2)^40` and satisfies `Err_K(N, n, A(n,N))`. -/
theorem theorem_8_5 (q K : ℕ) (hq : q.Prime) (hK : 1 ≤ K) (p₀ : Polynomial ℕ)
    (hp₀ : ShortRationalDisagreement p₀) :
    ∃ (P : Program) (k : ℕ) (hk : k < P.length), P.WF ∧ (P[k]'hk).sig = (1, 1, Srt.str) ∧
      Proves P (fun M => ∀ (n : M.N) (N : M.S),
        M.Net N n → M.le (M.numeral (q ^ K + 1)) n → M.le (M.depth N) (M.numeral K) →
        M.ValGood q N n →
        M.le (M.len (M.sfun (.defd k) [n] [N])) (M.pCut p₀ (M.len N)) ∧
          M.ErrK K N n (M.sfun (.defd k) [n] [N])) := by sorry

end ReLUWitness.Refuter
