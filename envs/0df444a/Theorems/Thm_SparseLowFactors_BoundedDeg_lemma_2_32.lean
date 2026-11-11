-- Prove2me | Theorems.Thm_SparseLowFactors_BoundedDeg_lemma_2_32
-- name    : SparseLowFactors.BoundedDeg.lemma_2_32
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:24:32.507871+00:00
-- url     : https://prove2.me/theorems/6acb3030-f91b-468a-9d60-7f098953916f
-- title:
--   Lemma 2.32 (division elimination) — removing division gates with sparse-product denominators at depth $\Delta+O(1)$
-- statement:
--   Let $\Gamma$ be a circuit with division gates over $F$ of size $m$ and depth at most $\Delta$, computing a polynomial $f\in F[X_1,\dots,X_n]$ of individual degree at most $d$. Suppose every denominator appearing at a division gate of $\Gamma$ is a product of $r$ polynomials, each $s$-sparse of individual degree at most $d$. There is a deterministic algorithm that, given $\Gamma$, runs in time $\mathrm{poly}(n,s,m,d,r)$ and outputs a circuit without division gates of size $\mathrm{poly}(n,m,d,r)$ and depth at most $\Delta+O(1)$ computing $f$.
--
--   Formally: universal $C,c_0$ and a fixed program $P$ such that for every field $F$ that is infinite or has $|F|>C(n+s+m+d+r)^C$, every $\Delta$, every such $\Gamma$ with $N$ nodes and every $w\ge C\log_2(n+s+m+N+d+r+2)$, $P$ run on $(n,s,d,r)$ and the encoding of $\Gamma$ halts within $C(n+s+m+N+d+r)^C$ steps without calling `factor`, and outputs a division-free circuit of size $\le C(n+m+d+r)^C$ and depth $\le\Delta+c_0$ computing $f$.
--
--   This is the second post-processing step of Algorithm 2.
--
--   Differences from the source:
--   - encoding: "there is an algorithm that runs in time …" → one fixed program P for the deterministic algebraic RAM (Machine), chosen before the field and the instance; time = number of executed instructions; reason: the paper names no machine; unit-cost field operations are its stated convention (p. 15)
--   - encoding: poly(·) and O(1) → C·(sum of the arguments)^C with one universal C, and one universal depth bound; reason: the paper defines poly(a_1,…,a_k) as (a_1+⋯+a_k)^c for an absolute constant c (p. 15)
--   - generalization: "depth at most a constant Δ"; poly(·) and O(1) may depend on the constant Δ → the constants C, c_0 are universal and the statement holds for every Δ; reason: for each fixed Δ this gives the printed statement
--   - reading: standing convention "the field we are working over is sufficiently large" (p. 15) → hypothesis: F infinite or |F| > C·(…)^C with the universal C; reason: the convention is stated once for the whole paper; the statement is the paper's over a large field
--   - encoding: no univariate factoring → the program makes no `factor` call; reason: the printed time bound has no T(F, d) term
--   - encoding: "computing a polynomial f" → Γ has no zero denominator and its rational function equals f; reason: Definition 2.5
--   - encoding: "a product of r many s-sparse polynomials" → a list of exactly r polynomials, each s-sparse of individual degree ≤ d, whose product (in F(X)) is the denominator; reason: literal reading
--   - encoding: given C → the input is (n, s, d, r) and the encoding of Γ (Machine definition); reason: input layout
--   - encoding: circuit of size m (number of wires) → the input circuit's node count N = Γ.numNodes joins the time bound (C·(n+s+m+N+d+r)^C) and the word-length bound (w ≥ C·log₂(n+s+m+N+d+r+2)); reason: a node not connected to the output adds no wire but still occupies input cells and needs a word-sized index (without N, two circuits whose node indices agree modulo 2^w have the same input memory and different values); a circuit all of whose nodes feed the output has N ≤ m + 1, where the bounds are the printed ones up to the universal constant
--   - encoding: word size not discussed → every word length w ≥ C·log₂(…); reason: indices and counters fit in a word, but words cannot encode field data
-- source:
--   Bhattacharjee, Kothary, Rai, Saraf, Deterministic Algorithms for Low Individual Degree Factors of Sparse Polynomials, arXiv:2606.27293 (held version, sha256 9837a932…), p. 26, Lemma 2.32

import Mathlib
import Definitions.Def_SetMultCost_Circuit
import Definitions.Def_SparseLowFactors_BoundedDeg_Sparse
import Definitions.Def_SparseLowFactors_BoundedDeg_Circuits
import Definitions.Def_SparseLowFactors_BoundedDeg_Machine

open SetMultCost

namespace SparseLowFactors.BoundedDeg

theorem lemma_2_32 :
    ∃ C c₀ : ℕ, ∃ P : List Instr,
    ∀ (F : Type) [Field F] (n s m d r Δ : ℕ),
      (Infinite F ∨ C * (n + s + m + d + r) ^ C < Nat.card F) →
      ∀ w : ℕ,
      ∀ fac : FactorOracle F, ∀ e : ℕ → F, EnumOK e →
      ∀ (Γ : DivCircuit (Fin n) F) (f : MvPolynomial (Fin n) F),
        Γ.size = m → Γ.depth ≤ Δ → Γ.Computes f → IndDegLE d f →
        (∀ q, Γ.IsDenominator q → ∃ qs : List (MvPolynomial (Fin n) F), qs.length = r ∧
          (∀ p ∈ qs, IsSparse s p ∧ IndDegLE d p) ∧
          q = algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F)) qs.prod) →
        C * Nat.log 2 (n + s + m + Γ.numNodes + d + r + 2) ≤ w →
      ∃ (T : ℕ) (res : Result F w),
        run P fac e T
          (loadWords w ([(n : ℤ), (s : ℤ), (d : ℤ), (r : ℤ)] ++ divCircuitWords (fun i => i.val) Γ))
          (loadFields (divCircuitFields Γ)) = some res ∧
        T ≤ C * (n + s + m + Γ.numNodes + d + r) ^ C ∧
        res.facCalls = 0 ∧
        ∃ Γ' : Circuit (Fin n) F, decodeCircuit n res.wm res.fm (outPtr res.wm) = some Γ' ∧
          Γ'.size ≤ C * (n + m + d + r) ^ C ∧ depth Γ' ≤ Δ + c₀ ∧ Γ'.value = f := by sorry

end SparseLowFactors.BoundedDeg
