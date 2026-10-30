-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P47_lemma18_associatedSymmetricChannel
-- name    : QAlgorithms.Papers.Independent.Bridge50.P47.lemma18_associatedSymmetricChannel
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:51:05.001757+00:00
-- url     : https://prove2.me/theorems/4c537e08-3565-4607-9dc3-359534ce0bc4
-- title:
--   Lemma 18: associated symmetric-channel factorization
-- statement:
--   Let $U:A'\to B\otimes E$ be a Stinespring isometry and $V:B\to F\otimes E'$ an isometric dilation of a degrading map to its actual complement. Assume their composite $T=(V\otimes I_E)U$ satisfies $(I_F\otimes\operatorname{SWAP}_{EE'})T=sT$ for one sign $s\in\{1,-1\}$. All physical systems are nonzero and finite. Take a reference $A\cong A'$ and a normalized test vector $\phi_0\in A\otimes A'$ of full input Schmidt rank. Form $\psi_0=(I_A\otimes T)\phi_0$ and let $G$ be the support of its $AF$ marginal; write $k=\dim G\ge1$ and identify $G'\cong G$. There exists an associated Stinespring isometry $W:G'\to E\otimes E'$ with $\operatorname{SWAP}W=sW$ such that every normalized $\phi\in A\otimes A'$ has a normalized vector $\xi\in G\otimes G'$ and an isometry $\widehat W:G\to A\otimes F$ satisfying
--
--   $$
--   (I_A\otimes T)\phi=(\widehat W\otimes W)\xi.
--   $$
--
--   The associated-channel condition identifies $G$ isometrically with the computed support and factors the constructed vector $\psi_0$ through $W$ with a chosen purification. Thus $W$ is fixed before $\phi$, whereas $\widehat W$ and $\xi$ may depend on $\phi$. This supplies a common symmetric channel for all test states.
-- source:
--   "Pretty strong" converse for the quantum capacity of degradable channels, arXiv:1301.4927v3, PDF p. 11, Lemma 18: associated symmetric-channel factorization

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P47

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Bridge50.P47

open QAlgorithms.Papers.Independent.Information100

variable {A B E F R I O : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

variable [Fintype R] [DecidableEq R] [Fintype I] [DecidableEq I]

variable [Fintype O] [DecidableEq O]

/-- Lemma 18, PDF p.11: G is the computed AF support. The reference is
an isomorphic copy of the whole input and has full input Schmidt support.
W is chosen before all subsequent test vectors; only xi and W-hat depend on phi. -/
theorem lemma18_associatedSymmetricChannel [Nonempty A] [Nonempty B] [Nonempty E]
    [Nonempty F] (U : Matrix (B × E) A ℂ) (V : Matrix (F × E) B ℂ)
    (negative : Bool) (hfactor : IsTypeIFactorization U V negative)
    (phi0 : EuclideanSpace ℂ (A × A)) (hphi0 : ‖phi0‖ = 1)
    (hfull : (traceRight (pureDensity phi0)).det ≠ 0) :
    let k := supportDimension U V phi0
    0 < k ∧ ∃ W : Matrix (E × E) (Fin k) ℂ,
      P67.IsIsometry W ∧ Associated U V phi0 W ∧
      P67.environmentSwap * W = swapSign negative • W ∧
      ∀ phi : EuclideanSpace ℂ (A × A), ‖phi‖ = 1 →
        ∃ What : Matrix (A × F) (Fin k) ℂ, P67.IsIsometry What ∧
        ∃ xi : EuclideanSpace ℂ (Fin k × Fin k), ‖xi‖ = 1 ∧
          testKet U V phi = WithLp.toLp 2 ((Matrix.kronecker What W).mulVec xi) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P47

end
