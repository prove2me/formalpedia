-- Prove2me | Theorems.Thm_RandomDimReduction_Channel_spechtModel_properties
-- name    : RandomDimReduction.Channel.spechtModel_properties
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T18:36:54.962089+00:00
-- url     : https://prove2.me/theorems/ac1150cf-4f74-489d-904b-04e18fd5496b
-- title:
--   Labelled Specht models are irreducible and pairwise inequivalent
-- statement:
--   Let $n$ be a positive integer. For each partition $\lambda\vdash n$, choose a unitary matrix model $\kappa_\lambda$ of the Specht representation $\mathrm{Sp}_\lambda$, with the labelling certified by unitary equivalence to the published Young-ideal construction. Then
--   $$\kappa_\lambda\ \text{is irreducible for every }\lambda\vdash n,$$
--   $$\lambda\ne\mu\quad\Longrightarrow\quad\kappa_\lambda\not\simeq\kappa_\mu.$$
--   Here irreducibility includes a nonzero carrier, and inequivalence rules out a unitary intertwiner between the two labelled models. These are the symmetric-group representation properties used in the Schur decomposition preceding Eq. (13). They allow the rectangular intertwiner lemma to be applied uniformly when comparing two ambient dimensions.
-- source:
--   Angus Lowe and Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), Section 5.1 p.15, Specht irreducibles in the Schur–Weyl decomposition preceding Eq.(13), used in Lemma 5.5 p.17. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf . Supporting character-projector identities: Keyl and Werner, Estimating the spectrum of a density operator, arXiv:quant-ph/0102027v1 p.2 Eqs.(2)–(4), already formalized as KWSpectrum.Estimator.eq_2_4_projections.

import Definitions.Def_RandomDimReduction_Channel_Schur
import Definitions.Def_RandomDimReduction_Channel_Representations

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem spechtModel_properties (n : ℕ) (hn : 0 < n) (κ : SpechtModel n) :
    (∀ lam : Shape n, Irreducible (κ.action lam)) ∧
    (∀ lam mu : Shape n, lam ≠ mu → Inequivalent (κ.action lam) (κ.action mu)) := by sorry

end RandomDimReduction.Channel
