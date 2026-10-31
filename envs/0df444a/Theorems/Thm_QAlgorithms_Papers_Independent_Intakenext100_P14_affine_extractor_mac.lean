-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P14_affine_extractor_mac
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P14.affine_extractor_mac
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:24:51.153351+00:00
-- url     : https://prove2.me/theorems/7fb70ae6-311e-4177-8a3a-69f15ab517b6
-- title:
--   Affine extractor MAC: authentication and classical/quantum extraction
-- statement:
--   Let $1\le\ell\le N$, choose fixed binary coordinates on $\mathbb F_{2^N}$, and let $[\cdot]$ project to the first $\ell$ bits. Let $K=(A,B)$ be independent and uniform, with $A\in\mathbb F_{2^N}$ and $B\in\mathbb F_2^\ell$. Define $\operatorname{MAC}_{A,B}(x)=[Ax]+B$. Impersonation succeeds with probability $2^{-\ell}$. After seeing the tag of a fixed message, any substitution strategy that selects a different message and a forged tag as functions of that observed tag also succeeds with probability $2^{-\ell}$.
--
--   Let $X,Z$ have any finite joint distribution, let $T=\operatorname{MAC}_K(X)$, and let $E$ be a normalized $q$-qubit state depending only on $X,Z$. The key is independent of $X,Z,E$. For every $\varepsilon\ge0$,
--
--   $$d_{\mathrm{TV}}((T,K,Z),(U,K,Z))\le\tfrac12\,2^{-\frac12(H_{\min}^{\varepsilon}(X\mid Z)-\ell)}+2\varepsilon,$$
--
--   $$\delta(\rho_{TKZE},\,2^{-\ell}I\otimes\rho_K\otimes\rho_{ZE})\le\tfrac12\,2^{-\frac12(H_{\min}^{\varepsilon}(X\mid Z)-q-\ell)}+2\varepsilon.$$
--
--   Here $U$ is a fresh independent uniform tag, entropy uses average guessing probability and event deletion without renormalization, and $\delta$ is half the trace norm. The Lean bounds use $\tfrac12\sqrt{2^\ell g_\varepsilon}$ and $\tfrac12\sqrt{2^{q+\ell}g_\varepsilon}$ with $g_\varepsilon=2^{-H_{\min}^{\varepsilon}(X\mid Z)}$; this includes $g_\varepsilon=0$ and entropy $+\infty$. This single result supplies both authentication and extraction; replay is excluded.
-- source:
--   Secure Identification and QKD in the Bounded-Quantum-Storage Model, arXiv:0708.2557v3, PDF p. 15, §4.3, unnumbered affine extractor-MAC example

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P14

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

open QAlgorithms.Papers.Independent.Gap48.P11 (blockMatrix cqDistance)

open QAlgorithms.Papers.Independent.Claimed50.P31 (bb84Vector)

open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Positive list length and inhabited fibers supply the tagged union's inhabitant.
This derived instance adds no hypothesis to Lemma 2.2. -/
local instance {m : ℕ} [NeZero m] {A : Fin m → Type*}
    [∀ i, Nonempty (A i)] : Nonempty (Sigma A) :=
  ⟨⟨0, Classical.choice (inferInstance : Nonempty (A 0))⟩⟩

/-- PDF p.15, the concrete affine extractor-MAC example. The authentication
probabilities include impersonation and adaptive DIFFERENT-message substitution.
The square-root bounds are exactly the displayed exponential bounds, expressed
via the retained guessing probability (zero means entropy +infinity). -/
theorem affine_extractor_mac
    {K : Type*} {S : Type} {Z : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]
    [Fintype S] [Nonempty S] [Fintype Z] [Nonempty Z]
    {N ell q : ℕ} (hpositive : 1 ≤ ell) (hell : ell ≤ N)
    (coordinates : K ≃ₗ[ZMod 2] (Fin N → ZMod 2))
    (p : Law S) (X : S → K) (z : S → Z)
    (rho : K → Z → Matrix (QAlgorithms.Qubits q) (QAlgorithms.Qubits q) ℂ)
    (hrho : ∀ x z, QAlgorithms.IsDensityMatrix (rho x z))
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    (∀ x : K, ∀ t : Fin ell → ZMod 2,
      keyMass (K := K) ell * ∑ key : K × (Fin ell → ZMod 2),
        (if affineTag coordinates hell key x = t then 1 else 0) = ((2 : ℝ) ^ ell)⁻¹) ∧
    (∀ x : K, ∀ change : (Fin ell → ZMod 2) → K,
      ∀ forge : (Fin ell → ZMod 2) → (Fin ell → ZMod 2),
      (∀ t, change t ≠ x) →
      keyMass (K := K) ell * ∑ key : K × (Fin ell → ZMod 2),
        (if affineTag coordinates hell key (change (affineTag coordinates hell key x)) =
          forge (affineTag coordinates hell key x) then 1 else 0) = ((2 : ℝ) ^ ell)⁻¹) ∧
    QAlgorithms.tvDist (classicalTagLaw coordinates hell p X z)
      (classicalIdealTagLaw (K := K) ell p z) ≤
        (1 / 2) * Real.sqrt ((2 : ℝ) ^ ell * smoothGuess p.prob X z epsilon) + 2 * epsilon ∧
    cqDistance (quantumTagLaw coordinates hell p X z rho)
      (quantumIdealTagLaw ell p X z rho) ≤
        (1 / 2) * Real.sqrt ((2 : ℝ) ^ (q + ell) * smoothGuess p.prob X z epsilon) +
          2 * epsilon := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P14

end
