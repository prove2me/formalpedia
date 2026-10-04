-- Prove2me | Theorems.Thm_TeschlQM_KatoRellich_second_resolvent_formula
-- name    : TeschlQM.KatoRellich.second_resolvent_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T22:38:32.699009+00:00
-- url     : https://prove2.me/theorems/f7954fbb-961a-4bea-81c3-885d6758e4c9
-- title:
--   Lemma 6.5 — the second resolvent formula
-- statement:
--   Let $A$ and $B$ be closed operators in a complex Hilbert space $\mathfrak{H}$ with $\mathfrak{D}(A) \subseteq \mathfrak{D}(B)$. Then for every $z \in \rho(A) \cap \rho(A + B)$ the **second resolvent formula** holds:
--   $$R_{A+B}(z) - R_A(z) = -R_A(z) B R_{A+B}(z) = -R_{A+B}(z) B R_A(z). \tag{6.4}$$
--
--   It compares the resolvents of an operator and of its perturbation, and is the starting point for relating their spectra.
--
--   **Formalization Note.** Stated vectorwise: for every $\varphi \in \mathfrak{H}$ the vectors $R_{A+B}(z)\varphi$ and $R_A(z)\varphi$ lie in $\mathfrak{D}(B)$ (so the products are everywhere defined) and both identities hold at $\varphi$. $A + B$ is Mathlib's sum of `LinearPMap`s on $\mathfrak{D}(A) \cap \mathfrak{D}(B)$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 135, Lemma 6.5, Eq. (6.4)

import Mathlib
import Definitions.Def_TeschlQM_KatoRellich_resolvent

namespace TeschlQM.KatoRellich

/-- Teschl, Lemma 6.5 and the second resolvent formula (6.4), p. 135. If `A` and `B` are closed
and `𝔇(A) ⊆ 𝔇(B)`, then for `z ∈ ρ(A) ∩ ρ(A + B)`
`R_{A+B}(z) - R_A(z) = -R_A(z) B R_{A+B}(z) = -R_{A+B}(z) B R_A(z)`;
each vector `R_{A+B}(z)φ`, `R_A(z)φ` lies in `𝔇(B)`, so both products are everywhere defined. -/
theorem second_resolvent_formula {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →ₗ.[ℂ] H) (hA : A.IsClosed) (hB : B.IsClosed)
    (hD : A.domain ≤ B.domain) (z : ℂ) (hzA : z ∈ resolventSet A)
    (hzAB : z ∈ resolventSet (A + B)) :
    (∀ φ : H, ∃ h : resolvent (A + B) z φ ∈ B.domain,
        resolvent (A + B) z φ - resolvent A z φ = -resolvent A z (B ⟨resolvent (A + B) z φ, h⟩)) ∧
      ∀ φ : H, ∃ h : resolvent A z φ ∈ B.domain,
        resolvent (A + B) z φ - resolvent A z φ = -resolvent (A + B) z (B ⟨resolvent A z φ, h⟩) := by sorry

end TeschlQM.KatoRellich
