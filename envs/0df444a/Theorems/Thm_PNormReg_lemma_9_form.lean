-- Prove2me | Theorems.Thm_PNormReg_lemma_9_form
-- name    : PNormReg.lemma_9_form
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:40:30.978142+00:00
-- url     : https://prove2.me/theorems/0dec6400-e0e0-4660-9ce9-ffb2aba26528
-- title:
--   Proof of Lemma 9, (17), pp.21–22 — eliminating the constraints: $\phi(u)=\mathrm{res}_p(Zu)$, $D\succeq0$, $\phi^\star=\mathrm{res}^\star_p$
-- statement:
--   Let $Z\in\mathbb R^{d\times k}$ have full column rank with $\mathrm{im}\,Z=\ker C$, and put
--
--   $$A:=NZ,\qquad h:=Z^\top g,\qquad D:=Z^\top RZ.$$
--
--   Then:
--
--   1. $u\mapsto Zu$ is a bijection from $\mathbb R^k$ onto $\ker C$;
--   2. $\phi(u):=h^\top u-u^\top Du-\|Au\|_p^p=\mathrm{res}_p(Zu)$ for all $u$;
--   3. $D\succeq0$;
--   4. $\phi$ attains its maximum, and $\phi^\star=\mathrm{res}^\star_p$;
--   5. $A$ has full column rank.
--
--   So each residual problem is an unconstrained maximization with the same value and the same approximation factors.
--
--   **Formalization Note** This item is the proof's display. The running-time clause of Lemma 9 is carried by Theorem 9, whose time bound contains it.
--
--   Differences from the source:
--   - generalization: C ∈ ℝ^{m×d} of full row rank with m < d and k = d − m → any C with any full column rank Z whose image is ker C; reason: the conclusion needs only Z; full row rank with m < d is one instance, as the page itself reduces to it by discarding redundant equations
--   - encoding: Lemma 9 (construction of Z, A, h, D in Õ(n^{ω(1,θ,θ)}) time) → the proof's display, for every such Z; the time clause is not in this item; reason: that clause is carried by PNormReg.theorem_9; it needs its own exponent and input format, and this item does not carry the number of Lemma 9
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Proof of Lemma 9, (17), pp.21–22 (PDF pp.22–23); Lemma 9, p.21

import Mathlib
import Definitions.Def_PNormReg_Regression
import Definitions.Def_PNormReg_Scaled

open Matrix

namespace PNormReg

/-- **Proof of Lemma 9**, (17), pp.21–22 (PDF pp.22–23).

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…).

For every full column rank `Z ∈ ℝ^{d×k}` with `im Z = ker C`, put `A := NZ`, `h := Z⊤g`, `D := Z⊤RZ`. Then
`u ↦ Zu` is a bijection from `ℝ^k` onto `ker C`, `φ(u) = res_p(Zu)` for all `u`, `D ⪰ 0`, `φ⋆` is attained
and equals `res⋆_p`, and `A` has full column rank.

**Formalization Note.** This is the proof's display; the time clause of Lemma 9 is carried by
`PNormReg.theorem_9`. `C` need not have full row rank: `k` is any size for which such a `Z` exists. -/
theorem lemma_9_form {n d m k : ℕ} (G : GenRegression n d m) (hG : G.IsStanding) (p : ℝ)
    (hp : 2 ≤ p) (x : Fin d → ℝ) (hx : G.Feasible x) (Z : Matrix (Fin d) (Fin k) ℝ)
    (hZ : Function.Injective Z.mulVec) (hrange : ∀ Δ, G.C *ᵥ Δ = 0 ↔ ∃ u, Z *ᵥ u = Δ) :
    let A : Matrix (Fin n) (Fin k) ℝ := G.N * Z
    let h : Fin k → ℝ := Zᵀ *ᵥ G.grad p x
    let D : Matrix (Fin k) (Fin k) ℝ := Zᵀ * G.hess p x * Z
    Set.BijOn Z.mulVec Set.univ {Δ | G.C *ᵥ Δ = 0} ∧
    (∀ u, phi h D A p u = G.res p x (Z *ᵥ u)) ∧
    D.PosSemidef ∧
    IsGreatest (Set.range (phi h D A p)) (phiStar h D A p) ∧
    phiStar h D A p = G.resStar p x ∧
    Function.Injective A.mulVec := by sorry

end PNormReg
