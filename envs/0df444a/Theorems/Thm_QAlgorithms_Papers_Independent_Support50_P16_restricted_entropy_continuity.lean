-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P16_restricted_entropy_continuity
-- name    : QAlgorithms.Papers.Independent.Support50.P16.restricted_entropy_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:57:52.328345+00:00
-- url     : https://prove2.me/theorems/fe2f38b0-0a94-4ede-aa4e-85b833f6d2c1
-- title:
--   Proposition 3: continuity under an arbitrary measurement class
-- statement:
--   Let $k\ge1$ be a finite Hilbert-space dimension and $\tau=I/k$. Let $\mathcal G$ be any set of density matrices containing $\tau$, star-shaped about $\tau$: $p\sigma+(1-p)\tau\in\mathcal G$ whenever $\sigma\in\mathcal G$ and $0\le p\le1$. Let $\mathcal M$ be any class of normalized finite-outcome POVMs, possibly empty. Define $E_{r,\mathcal M}^{(\mathcal G)}(\rho)=\inf_{\sigma\in\mathcal G}\sup_{M\in\mathcal M}D(M(\rho)\Vert M(\sigma))$ and $\|\rho-\rho'\|_{\mathcal M}=\sup_{M\in\mathcal M}\|M(\rho)-M(\rho')\|_1$, with empty nonnegative supremum zero. For density matrices $\rho,\rho'$ and $\|\rho-\rho'\|_{\mathcal M}\le\epsilon\le1/e$, both optimized entropies are finite and
--
--   $$
--   \left|E_{r,\mathcal M}^{(\mathcal G)}(\rho)-E_{r,\mathcal M}^{(\mathcal G)}(\rho')\right|\le\omega_k(\epsilon),\qquad
--   \omega_k(\epsilon)=\begin{cases}2\epsilon\log_2(6k/\epsilon),&\epsilon>0,\\0,&\epsilon=0.\end{cases}
--   $$
--
--   Here $e$ is the base of the natural logarithm. This continuity bound does not require $\mathcal G$ to be closed or convex, or $\mathcal M$ to distinguish every state.
-- source:
--   Relative entropy and squashed entanglement, arXiv:1210.3181v2, PDF p. 5, Proposition 3: continuity under an arbitrary measurement class

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P16

namespace QAlgorithms.Papers.Independent.Support50.P16

noncomputable section

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "tau" => QAlgorithms.Papers.Independent.Information100.P76.maximallyMixed

local notation "RE" => QAlgorithms.Papers.Independent.Information100.P54.relativeEntanglement

local notation "RER" => QAlgorithms.Papers.Independent.Information100.P54.regularizedEntanglement

local notation "SQ" => QAlgorithms.Papers.Independent.Dependency50.P19.squashed

local notation "CMI" => QAlgorithms.Papers.Independent.Dependency50.P19.conditionalMutual

local notation "MI" => QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation

local notation "LOCC" => QAlgorithms.Papers.Independent.Information100.P21.FiniteLOCC

local notation "power" => QAlgorithms.Papers.Independent.Dependency50.P42.dimensionedPower

local notation "index" => QAlgorithms.Papers.Independent.Dependency50.P42.copyIndex

-- Accepted matrix coordinates (not P50.Bipartite, which is a vector space).

local notation "Bipartite" => QAlgorithms.Papers.Independent.Dependency50.P50.BipartiteMat

-- Positive outcome counts follow already from a POVM on a nonzero register.

local notation "FiniteMeasurement" => QAlgorithms.Papers.Independent.Information100.P04.Measurement

local notation "relative" =>
  ((fun _ _ rho => RE rho) : ExtendedEntanglementFunctional)

-- Reuse the accepted operational/variational quantity through a typed notation.

local notation "squashed" =>
  ((fun _ _ rho => ENNReal.ofReal (SQ rho)) : ExtendedEntanglementFunctional)

local notation "originalMarginal" => QAlgorithms.Papers.Independent.Information100.P04.principalMarginal

-- Exact accepted partial trace of the same AA'BB' extension.

local notation "ancillaryMarginal" => QAlgorithms.Papers.Independent.Information100.P04.ancillaryMarginal

local notation "distillable" =>
  ((fun _ _ rho => ENNReal.ofReal (QAlgorithms.Papers.Independent.Gap48.P32.twoWayDistillable rho)) : ExtendedEntanglementFunctional)

local notation "cost" =>
  ((fun _ _ rho => ENNReal.ofReal (QAlgorithms.Papers.Independent.Dependency50.P42.alternativeCost
    (fun _ _ X Y => traceNorm (X-Y)) rho)) : ExtendedEntanglementFunctional)

/-- Proposition 3, PDF p.5 (announced p.4); proof pp.10--11.
Star-shaped G may be nonconvex and nonclosed; M may be empty. Finite values
are conclusions, before their toReal difference is used. -/
theorem restricted_entropy_continuity (k : ℕ+)
    (G : Set (Matrix (Fin (k : ℕ)) (Fin (k : ℕ)) ℂ))
    (M : Set (FiniteMeasurement (Fin (k : ℕ))))
    (hstates : ∀ sigma ∈ G, IsDensityMatrix sigma)
    (htau : tau k ∈ G)
    (hstar : ∀ sigma ∈ G, ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      (p : ℂ) • sigma + ((1-p : ℝ) : ℂ) • tau k ∈ G)
    (rho sigma : Matrix (Fin (k : ℕ)) (Fin (k : ℕ)) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (epsilon : ℝ) (heps0 : 0 ≤ epsilon)
    (hdistance : measurementDistance M rho sigma ≤ epsilon)
    (heps1 : epsilon ≤ 1 / Real.exp 1) :
    restrictedEntropy G M rho ≠ ⊤ ∧ restrictedEntropy G M sigma ≠ ⊤ ∧
    |(restrictedEntropy G M rho).toReal - (restrictedEntropy G M sigma).toReal| ≤
      continuityModulus k epsilon := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P16
