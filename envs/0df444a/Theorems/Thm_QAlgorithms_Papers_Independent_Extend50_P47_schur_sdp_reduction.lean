-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P47_schur_sdp_reduction
-- name    : QAlgorithms.Papers.Independent.Extend50.P47.schur_sdp_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:29:08.994609+00:00
-- url     : https://prove2.me/theorems/4d40b18a-dc11-4cfb-9ba8-918a931e430b
-- title:
--   Isotypic block reduction of symmetry SDPs, (146)–(157)
-- statement:
--   Every register has a fixed finite nonempty computational basis. States are positive semidefinite trace-one matrices, and pure vectors have norm one. Write $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ for squared fidelity. Here $G$ is a finite group and $U$ denotes its specified unitary representation. Raw Bose averages $\Pi=|G|^{-1}\sum_gU(g)$ use an ordinary representation; conjugation symmetry permits a projective representation.
--
--   There exist isotypic decomposition data with the stated irreducibility, intertwining, and inequivalence conditions. The invariant densities have exactly the following multiplicity-block parameterization; the twirl and the ordinary Bose support parameterizations hold for the same data.
--
--   $$
--   U(g)=W\!\left(\bigoplus_\lambda I_{m_\lambda}\otimes U_\lambda(g)\right)W^\dagger,\qquad\sigma=W\!\left(\bigoplus_\lambda b_\lambda\otimes\frac{I_{d_\lambda}}{d_\lambda}\right)W^\dagger,\quad b_\lambda\succeq0,\quad\sum_\lambda\operatorname{Tr}b_\lambda=1.
--   $$
--
--   The families $U_\lambda$ are irreducible and pairwise inequivalent; $m_\lambda,d_\lambda>0$. The twirl uses blocks $b_\lambda=\operatorname{Tr}_2[(W^\dagger\sigma W)_{\lambda\lambda}]$. Bose support restricts blocks to trivial irreps only for an ordinary representation.
-- source:
--   Testing symmetry on quantum computers, arXiv:2105.12758v3, PDF p. 18, Isotypic block reduction of symmetry SDPs, (146)–(157)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P47

open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

variable {G S R P T A B C D R2 S2 : Type*}

variable [Fintype G] [Group G] [DecidableEq G]

variable [Fintype S] [DecidableEq S] [Nonempty S]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype P] [DecidableEq P] [Nonempty P]

variable [Fintype T] [DecidableEq T] [Nonempty T]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

variable [Fintype R2] [DecidableEq R2] [Nonempty R2]

variable [Fintype S2] [DecidableEq S2] [Nonempty S2]

/-- PDF pp.18–19, (146)–(157): construct isotypic data and give the reduced
state and twirl parameterizations. Projective symmetry data are permitted;
the Bose specialization explicitly requires an ordinary law. -/
theorem schur_sdp_reduction [Nonempty S] (U : G → Matrix.unitaryGroup S ℂ) (hU : IsProjectiveUnitaryLift U) :
    ∃ E : IsotypicData (fun g => (U g : Mat S)),
      (∀ rho, IsDensityMatrix rho →
        (Sym (fun g => (U g : Mat S)) rho ↔
          ∃ b : (l : Fin E.count) → Mat (Fin (E.mult l)),
            (∀ l, (b l).PosSemidef) ∧ (∑ l, (b l).trace = 1) ∧ rho = isotypicDensity E b)) ∧
      (∀ rho : Mat S, (Fintype.card G : ℂ)⁻¹ •
        ∑ g, (U g : Mat S) * rho * (U g : Mat S)ᴴ = isotypicDensity E (schurBlocks E rho)) ∧
      ((∀ g h, (U (g * h) : Mat S) = (U g : Mat S) * (U h : Mat S)) →
        ∀ rho, IsDensityMatrix rho →
          (Bose (symmetryControlAverage (fun g => (U g : Mat S))) rho ↔
            ∃ b : (l : Fin E.count) → Mat (Fin (E.mult l)),
              (∀ l, (b l).PosSemidef) ∧ (∑ l, (b l).trace = 1) ∧
              (∀ l, ¬ TrivialBlock E l → b l = 0) ∧ rho = isotypicDensity E b)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P47

end
