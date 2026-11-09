-- Prove2me | Theorems.Thm_QCSepTotal_theorem_1_4
-- name    : QCSepTotal.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:41:59.944814+00:00
-- url     : https://prove2.me/theorems/dd973bc6-892b-42d9-a897-72fe12fdeb2c
-- title:
--   Theorem 1.4 — partial-to-total conversion: $N=\tilde O(n+s)$, $R(F_{\mathrm{tot}})=\tilde\Omega(R(F))$, $Q_{r+1}(F_{\mathrm{tot}})=\tilde O(q)$
-- statement:
--   Let $F:\{0,1\}^n\times\{0,1\}^n\to\{0,1,*\}$ be a partial function. Suppose its domain indicator $D_F(x,y)=\mathbf 1[(x,y)\in\mathrm{dom}(F)]$ has a Boolean circuit of size at most $s$, where $s$ is a positive integer with $s\le\mathrm{poly}(n)$, and $F$ has an $r$-message quantum protocol of cost $q\ge1$, where $r\ge1$. Then there is a total function $F_{\mathrm{tot}}:\{0,1\}^N\times\{0,1\}^N\to\{0,1\}$ with
--   $$N=\tilde O(n+s),\qquad R(F_{\mathrm{tot}})=\tilde\Omega(R(F)),\qquad Q_{r+1}(F_{\mathrm{tot}})=\tilde O(q).$$
--
--   Explicitly: for every $C$ there is a constant $K$ such that for all $n\ge2$, every such $F$, every $1\le s\le n^C$ and all $r,q\ge1$ with $Q_r(F)\le q$, there is a total $F_{\mathrm{tot}}$ on $N$ bits per party with
--   $$N\le K(n+s)(\log n)^K,\qquad R(F)\le K(\log n)^K R(F_{\mathrm{tot}}),\qquad Q_{r+1}(F_{\mathrm{tot}})\le K\,q\,(\log n)^K .$$
--
--   This converts quantum-versus-randomized separations for partial functions into separations for total functions, with only polylogarithmic loss; applied to suitable partial functions it yields Theorems 1.2 and 1.3.
--
--   **Formalization Note** $\tilde O$ suppresses factors polynomial in $\log n$ (footnote 1, p.1); one constant $K$, depending only on the degree $C$ of the polynomial bound on $s$, is chosen before $n, F, s, r, q$. $Q_r$ counts protocols with at most $r$ messages (p.1). The circuit reads Alice's bits and Bob's bits as its $2n$ inputs.
--
--   Differences from the source:
--   - reading: Õ(·), Ω̃(·) and s ≤ poly(n) → explicit factors (log₂ n)^K with one K depending only on C, where s ≤ n^C; reason: footnote 1: the notation suppresses factors polynomial in log n
--   - reading: the asymptotic statement → every n ≥ 2; reason: for bounded n all quantities are bounded (R(F) ≤ n + 1), so the constant absorbs them; n ≥ 2 keeps log₂ n > 0
--   - generalization: F has an r-message quantum protocol of cost q → Q_r(F) ≤ q: a protocol with at most r messages and cost at most q; reason: a protocol with exactly r messages and cost q qualifies
--   - encoding: {0,1}^n and the domain indicator circuit → Fin n → Bool, a circuit on the 2n inputs Fin n ⊕ Fin n; reason: same inputs
--   - encoding: R(·) and Q_r(·) of p.5 (the output produced by a party; the quantum protocol with private randomness and intermediate measurements) → R over randomized protocols whose output is the leaf label (finite public and private coin types), Q_r over the owned-qubit unitary model with start state |0…0⟩ and one final measurement by the last receiver; reason: a party's final output can be sent as one more bit, so the two R differ by at most 1 and R(Ftot) ≥ 1 whenever R(F) ≥ 1; randomness and measurements are simulated unitarily (deferred measurement); the constant K absorbs both
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), Theorem 1.4, p.2

import Mathlib
import Definitions.Def_QCSepTotal_RandProtocol
import Definitions.Def_QCSepTotal_QProtocol
import Definitions.Def_QCSepTotal_Circuit

namespace QCSepTotal

/-- **Theorem 1.4** (F. Le Gall, *Improved Separations between Quantum and Classical Communication Complexity of Total Functions*, arXiv:2609.16726 (held version, sha256 970e1476…), p.2). Let `F : {0,1}ⁿ × {0,1}ⁿ → {0, 1, ∗}` be a
partial function. Suppose its domain indicator `D_F(x, y) = 1[(x, y) ∈ dom(F)]` has a Boolean
circuit of size at most `s`, where `s` is a positive integer with `s ≤ poly(n)`, and `F` has an
`r`-message quantum protocol of cost `q ≥ 1`, where `r ≥ 1`. There is a total function
`Ftot : {0,1}^N × {0,1}^N → {0,1}` with `N = Õ(n + s)`, `R(Ftot) = Ω̃(R(F))`,
`Q_{r+1}(Ftot) = Õ(q)`.

**Formalization Note.** Õ suppresses factors polynomial in `log n` (footnote 1, p.1): for each
degree `C` of the polynomial bound `s ≤ n^C` there is one constant `K`, chosen before `n, F, s,
r, q`, with `N ≤ K (n + s) (log₂ n)^K`, `R(F) ≤ K (log₂ n)^K R(Ftot)` and `Q_{r+1}(Ftot) ≤
K q (log₂ n)^K`. `Q_r` counts protocols with at most `r` messages (p.1). `n ≥ 2` keeps
`log₂ n > 0`; for bounded `n` all quantities are bounded, so this is the asymptotic statement.
The circuit reads Alice's bits on `Sum.inl` and Bob's on `Sum.inr`. -/
theorem theorem_1_4 :
    ∀ C : ℕ, ∃ K : ℕ, ∀ n : ℕ, 2 ≤ n → ∀ F : PartialFn (Fin n → Bool) (Fin n → Bool), ∀ s : ℕ,
      1 ≤ s → s ≤ n ^ C →
      (∃ circ : Circuit (Fin n ⊕ Fin n), circ.size ≤ s ∧
        ∀ x y, circ.eval (Sum.elim x y) = (F x y).isSome) →
      ∀ r q : ℕ, 1 ≤ r → 1 ≤ q → HasQProtocol F r q →
      ∃ N : ℕ, ∃ Ft : (Fin N → Bool) → (Fin N → Bool) → Bool,
        (N : ℝ) ≤ K * ((n : ℝ) + s) * Real.logb 2 n ^ K ∧
        (R F : ℝ) ≤ K * Real.logb 2 n ^ K * R (total Ft) ∧
        HasQProtocol (total Ft) (r + 1) ⌊(K : ℝ) * q * Real.logb 2 n ^ K⌋₊ := by sorry

end QCSepTotal
