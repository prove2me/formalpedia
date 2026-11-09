-- Prove2me | Theorems.Thm_RobustFracMP_lemma_3_1
-- name    : RobustFracMP.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:00:31.43564+00:00
-- url     : https://prove2.me/theorems/958f0b46-f788-4b89-9e87-e7678d4ef3ba
-- title:
--   Lemma 3.1 — scaled Mettu–Plaxton stays an LMP $2^{O(z^2)}\varepsilon^{-2z}$-approximation under distance distortion
-- statement:
--   There is an absolute constant $C$ with the following property. Let $z\ge1$ be an integer, $(P,\mathrm{dist})$ a finite nonempty metric space, $\lambda>0$ an opening cost and $\varepsilon\in(0,1)$, and let $\widetilde{\mathrm{dist}}:P\times P\to\mathbb R$ be a distorted distance with
--
--   $$\mathrm{dist}(p,q)\le\widetilde{\mathrm{dist}}(p,q)\le\varepsilon^{-2}\,\mathrm{dist}(p,q)\qquad\text{for all }p,q\in P.\qquad(9)$$
--
--   Let $\tilde y\in\mathbb R^P$ be the output of Algorithm 1 ($\mathrm{MP}_\beta$) with scale factor $\beta=2^{-z-1}\varepsilon^{2z}$ run on $(P,\widetilde{\mathrm{dist}})$, that is, $\tilde y_p=\tilde r_p/\lambda$ with $\sum_{q}[\tilde r_p-\beta\,\widetilde{\mathrm{dist}}(p,q)^z]_+=\lambda$. Then $\tilde y$ is a fractional solution of Power-$z$ Facility Location ($\tilde y\ge0$ and $\|\tilde y\|_1\ge1$), and
--
--   $$\mathrm{cost}_z(\tilde y)\le2^{Cz^2}\,\varepsilon^{-2z}\bigl(\widehat{\mathrm{OPT}}^{\mathrm{fl}}_z(\lambda)-\lambda\|\tilde y\|_1\bigr),$$
--
--   where $\mathrm{cost}_z$ and $\widehat{\mathrm{OPT}}^{\mathrm{fl}}_z$ are computed with the true distance $\mathrm{dist}$.
--
--   This is the paper's main technical contribution: an algorithm that only sees a distorted, possibly asymmetric distance still returns an LMP approximation for the true metric, with a guarantee independent of the size of $P$. The paper uses it, with distances rounded to powers of $\varepsilon^{-1}$, for its MPC algorithms (Corollary 3.2 and Theorem 5.1), which are not part of this statement.
--
--   **Formalization Note** $\widetilde{\mathrm{dist}}$ is any real function satisfying (9); it is not assumed symmetric or a metric. $\varepsilon^{-2z}$ is $(\varepsilon^{2z})^{-1}$ and $2^{Cz^2}$ is a real power.
--
--   Differences from the source:
--   - reading: 2^{O(z²)} → 2^{C·z²} for one real constant C, quantified before P, z and all other data; reason: O(z²) hides an absolute constant; the paper's constants (γ* = 2^{2z²+z}, 2^{O(z)}) do not depend on P, λ, β or ε
--   - reading: 'Let ε ∈ (0, 1) be a constant' → for every ε with 0 < ε < 1, after the constant C; reason: the constant hidden in 2^{O(z²)} does not depend on ε; the dependence on ε is the explicit factor ε^{−2z}
--   - encoding: 'ỹ is a fractional solution to Power-z Facility Location' → (∀ p, 0 ≤ ỹ p) ∧ 1 ≤ ∑ p, ỹ p; reason: fractional solutions are y ∈ ℝ^P_{≥0} with ‖y‖₁ ≥ 1 (p.11)
--   - encoding: ‖y‖₁ for y ≥ 0 → ∑ p, y p; reason: the entries are nonnegative, so the sum is the ℓ₁ norm
--   - encoding: a dataset P in a metric space (finite; a fractional solution with ‖y‖₁ ≥ 1 exists) → P a type with Fintype, Nonempty and MetricSpace instances; reason: the dataset is a finite set of points; nonemptiness only excludes the empty dataset, which has no fractional solution
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Lemma 3.1, p.12 (PDF p.14), restated p.24 (PDF p.26)

import Mathlib
import Definitions.Def_RobustFracMP_fracCost
import Definitions.Def_RobustFracMP_optFL
import Definitions.Def_RobustFracMP_mpOutput

set_option autoImplicit false

namespace RobustFracMP

universe u

/-- **Lemma 3.1 (scaled Mettu–Plaxton is a robust LMP approximation under distance distortion).**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering*,
arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Lemma 3.1, p.12 (PDF p.14; restated p.24): "Let ε ∈ (0, 1) be a constant and suppose that a
distorted distance function \tilde{dist} satisfies dist(p, q) ≤ \tilde{dist}(p, q) ≤ ε^{−2} ·
dist(p, q), ∀p, q ∈ P. (9) Let ỹ ∈ ℝ^P_{≥0} denote the output of MP_β (Algorithm 1) with
β := 2^{−z−1} · ε^{2z} on input (P, \tilde{dist}) (instead of (P, dist)). Then ỹ is a fractional
solution to Power-z Facility Location with an LMP 2^{O(z²)}ε^{−2z}-approximation guarantee on the
original metric space, i.e., cost_z(ỹ) ≤ 2^{O(z²)}ε^{−2z} · (\widehat{OPT}^{fl}_z(λ) − λ · ‖ỹ‖₁),
where both cost_z(ỹ) and \widehat{OPT}^{fl}_z(λ) are evaluated with respect to the original
distance dist."

Every clause is stated: `ỹ ≥ 0`, `‖ỹ‖₁ ≥ 1` (ỹ is a fractional solution), and the LMP inequality,
with cost and OPT in `dist` and MP_β run on `distT`.

**Formalization Note.** `2^{O(z²)}` is `2^{C·z²}` for one absolute real constant `C`, quantified
before the space, `z`, `ε`, `λ` and `\tilde{dist}`; "ε a constant" is read as "for every
ε ∈ (0, 1)". `(P, dist)` is a finite nonempty metric space (the dataset, `F = P`), `z ≥ 1` an
integer, `λ > 0`. `distT : P → P → ℝ` is any function satisfying (9); it is not assumed symmetric
or a metric. `ε^{−2}` is `(ε ^ 2)⁻¹`, `ε^{−2z}` is `(ε ^ (2 * z))⁻¹`, `2^{−z−1}` is `1 / 2 ^ (z + 1)`,
`‖ỹ‖₁` is `∑ p, ỹ p`. -/
theorem lemma_3_1 : ∃ C : ℝ, ∀ (P : Type u) [Fintype P] [Nonempty P] [MetricSpace P] (z : ℕ),
    1 ≤ z → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ lam : ℝ, 0 < lam → ∀ distT : P → P → ℝ,
      (∀ p q, dist p q ≤ distT p q ∧ distT p q ≤ (ε ^ 2)⁻¹ * dist p q) →
      (∀ p, 0 ≤ mpOutput z distT (1 / 2 ^ (z + 1) * ε ^ (2 * z)) lam p) ∧
      1 ≤ ∑ p, mpOutput z distT (1 / 2 ^ (z + 1) * ε ^ (2 * z)) lam p ∧
      fracCost z (mpOutput z distT (1 / 2 ^ (z + 1) * ε ^ (2 * z)) lam) ≤
        (2 : ℝ) ^ (C * (z : ℝ) ^ 2) * (ε ^ (2 * z))⁻¹ *
          (optFL P z lam - lam * ∑ p, mpOutput z distT (1 / 2 ^ (z + 1) * ε ^ (2 * z)) lam p) := by sorry

end RobustFracMP
