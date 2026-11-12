-- Prove2me | Theorems.Thm_PQNormIPM1352_Main_lemma_15
-- name    : PQNormIPM1352.Main.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:22.910035+00:00
-- url     : https://prove2.me/theorems/021378ef-d66a-4ccb-8cfd-193adc889b6e
-- title:
--   Lemma 15 — termination: $\lambda_\eta(x)\le1/10\Rightarrow\langle c,x\rangle-\langle c,x^*\rangle\le 7\nu/(6\eta)$
-- statement:
--   Let $F$ be a $\nu$-self-concordant barrier for $K\subseteq\mathbb R^N$ with invertible Hessian on $\mathrm{int}(K)$, let $c\in\mathbb R^N$, and let $x^*\in K$ minimize $\langle c,\cdot\rangle$ over $K$. For every $x\in\mathrm{int}(K)$ and $\eta > 0$ with $\lambda_\eta(x)\le 1/10$,
--   $$\langle c, x\rangle - \langle c, x^*\rangle \le \frac{7\nu}{6\eta}.$$
--
--   It converts the invariant of Theorem 12 into an optimality gap, and needs no rounding at termination.
--
--   Differences from the source:
--   - reading: H(x)⁻¹ in λ_η(x) → hypothesis: the Hessian is positive definite on int(K); reason: the Newton decrement presupposes an invertible Hessian; with Mathlib's junk inverse a singular Hessian would give λ = 0 at every point
--   - encoding: x* = argmin_{x∈K}⟨c, x⟩ → a point x* ∈ K with ⟨c, x*⟩ ≤ ⟨c, y⟩ for all y ∈ K; reason: the minimizer is a hypothesis, as in §2.2.2
-- source:
--   Marco Pirazzini, Daniel Spielman, A Fast and Accurate Algorithm for the p → q Norm of Sparse Non-Negative Matrices, STOC 2027 submission #1352 (October 2026), Lemma 15, printed p. 24 (PDF p. 25)

import Mathlib
import Definitions.Def_PQNormIPM1352_Main_IPM

open scoped RealInnerProductSpace

namespace PQNormIPM1352.Main

/-- **Lemma 15** (termination; Pirazzini–Spielman, STOC 2027 #1352, p. 24). Let `F` be a
`ν`-self-concordant barrier for `K` with invertible Hessian, `c ∈ ℝᴺ`, and `x* ∈ K` a minimizer of
`⟨c, ·⟩` over `K`. For every `x ∈ int(K)` and `η > 0` with `λ_η(x) ≤ 1/10`,
`⟨c, x⟩ − ⟨c, x*⟩ ≤ 7ν / (6η)`. -/
theorem lemma_15 {N : ℕ} (K : Set (Vec N)) (F : Vec N → ℝ) (ν : ℝ) (hF : IsNuSCB K F ν)
    (hH : ∀ y ∈ interior K, (hessMat F y).PosDef) (c xstar : Vec N) (hxs : xstar ∈ K)
    (hmin : ∀ y ∈ K, ⟪c, xstar⟫ ≤ ⟪c, y⟫) (x : Vec N) (hx : x ∈ interior K) (η : ℝ)
    (hη : 0 < η) (hdec : newtonDecrement (penalized F c η) x ≤ 1 / 10) :
    ⟪c, x⟫ - ⟪c, xstar⟫ ≤ 7 * ν / (6 * η) := by sorry

end PQNormIPM1352.Main
