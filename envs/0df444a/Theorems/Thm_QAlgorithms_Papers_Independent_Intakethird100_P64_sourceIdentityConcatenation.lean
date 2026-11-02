-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P64_sourceIdentityConcatenation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P64.sourceIdentityConcatenation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:35:16.932685+00:00
-- url     : https://prove2.me/theorems/39d0fbbf-9c20-4894-846f-191760acec32
-- title:
--   Concatenating a source identity with a relative communication identity
-- statement:
--   Let $S$ be a finite nonzero source register with density matrix $\rho$, purified by a unit vector $|\phi\rangle^{RS}$. The reference $R$ is inaccessible to Alice and Bob. The registers $\widehat A,A',B,\widehat B$ are identified copies of $S$, so the two occurrences of $\rho$ denote the same density under relabeling. Then
--
--   $$
--   \langle\mathrm{id}^{S\to\widehat A}:\rho\rangle+
--   \langle\mathrm{id}^{A'\to B}:\rho\rangle
--   \ge\langle\mathrm{id}^{S\to\widehat B}:\rho\rangle.
--   $$
--
--   For every positive error and rate slack, all sufficiently large positive $n$ have local encoding and decoding maps using $n$ supplied identity-channel calls on the $n$ Source-supplied systems. For every positive input-promise tolerance $\eta$, the actual encoded input marginal is within $\eta$ of $\rho^{\otimes n}$. The code succeeds jointly with $R^n$ for every physical implementation of the relative identity satisfying its joint error guarantee on inputs with that near-IID marginal. The local maps are chosen before that implementation is supplied. No additional communication or shared state is supplied.
--
--   This is direct routing of the specified source, rather than a general transitivity principle for arbitrary resources.
-- source:
--   A triangle of dualities: reversibly decomposable quantum channels, source-channel duality, and time reversal, arXiv:quant-ph/0505138v1, PDF p. 3, Fully quantum Slepian-Wolf preamble: source/identity concatenation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P64

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P64

open QAlgorithms

open QAlgorithms.Papers.Independent.Gap48.P20
  (Copies redistributionMarginal subsystemEntropy forwardApply)

open QAlgorithms.Papers.Independent.Dependency50.P48 (densityPower)

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, unnumbered display and Fig.3: concatenate the Source-to-Alice
identity with the relative Alice-to-Bob identity for the same rho. The actual
source purification and the encoder's marginal are part of the operational test. -/
theorem sourceIdentityConcatenation {R S : Type} [Fintype R] [Fintype S]
    [Nonempty R] [Nonempty S] (phi : EuclideanSpace ℂ (R × S))
    (hphi : IsState phi) : SourceRoutingAchievable phi := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P64

end
