-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P29_canonical_effective_channel
-- name    : QAlgorithms.Papers.Independent.Next46.P29.canonical_effective_channel
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:14:09.454722+00:00
-- url     : https://prove2.me/theorems/5c6ab7d9-b092-430d-9b2a-def9ee7d2ece
-- title:
--   Canonical-token effective channel
-- statement:
--   Let $G$ be a compact Lie group with normalized Haar measure $dg$. Fix a finite nonempty family of inequivalent continuous unitary irreducible representations of positive dimensions $d_q$, and use exactly the paired token space $\bar H_R=\bigoplus_q M_q\otimes\bar N_q$, with $\dim\bar N_q=d_q$. Put $D_R=\sum_qd_q^2$ and $|e\rangle=\sum_q\sqrt{d_q/D_R}\sum_m|q,m\rangle|\phi_{q,m}\rangle$. Let $U_S$ be any continuous unitary representation on a message space of dimension $d_S>0$. Write $|g\rangle=U_R(g)|e\rangle$ and $K_g=|g\rangle\otimes U_S(g)$. Define $\mathcal E(X)=\int K_gXK_g^\dagger dg$ and $\mathcal R(Y)=D_R\int K_g^\dagger YK_g dg$. Then $e$ is normalized, both maps are quantum channels, $\mathcal R=D_R\mathcal E^\dagger$ for the Hilbert–Schmidt adjoint, and for every density operator $\rho$,
--
--   $$\mathcal R\mathcal E(\rho)=\int_G p(g)U_S(g)\rho U_S(g)^\dagger dg,\qquad p(g)=D_R|\langle e|g\rangle|^2,\qquad\int_Gp(g)dg=1.$$
--
--   This characterizes the effective noise for the fixed canonical token and decoder. In addition, $p(hgh^{-1})=p(g)$ for all $g,h$, and $\mathcal R\mathcal E$ commutes with conjugation by $U_S(h)$. For each covariant measurement outcome $h$, the normalized conditional output $D_R\int |\langle h|g\rangle|^2 U_S(h^{-1}g)\rho U_S(h^{-1}g)^\dagger dg$ equals the same effective channel output; it is independent of $h$.
-- source:
--   Quantum communication using a bounded-size quantum reference frame, arXiv:0812.5040v2, PDF p. 1, Paper result: canonical-token effective channel, Eqs.(1)–(3), (38)–(40)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P29

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Next46.P29

open QAlgorithms.Papers.Independent.Information100.P56 (IsIrreducible)

open QAlgorithms.Papers.Independent.Information100.P63 (mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P71 (IsSubchannel)

attribute [local instance] Classical.decEq Classical.propDecidable

section GeneralResults

variable {G : Type*} [Group G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hCompact : CompactSpace G] [hT2 : T2Space G] [MeasurableSpace G] [hBorel : BorelSpace G]
  (mu : Measure G) [hHaar : Measure.IsHaarMeasure mu] [hProb : IsProbabilityMeasure mu]

include hTop hCompact hT2 hBorel hHaar hProb

/-- PDF pp.1–2 and pp.8–9, Eqs.(1)–(3),(38)–(40): canonical token encoding,
Hilbert–Schmidt adjoint recovery and the exactly normalized effective channel.
The overlap is conjugation-invariant, the channel is covariant, and the normalized
conditional output is independent of the covariant measurement outcome (p.9).
No optimization over token preparations is claimed. -/
theorem canonical_effective_channel (hLie : HasLieStructure G)
    (C : CanonicalToken G) {s : ℕ} (hs : 0 < s) (U : BasedUnitaryRep G s) :
    IsState (canonicalKet C) ∧
    IsChannel (canonicalEncoding mu C U) ∧ IsChannel (canonicalRecovery mu C U) ∧
    (∀ A B, (Aᴴ * canonicalRecovery mu C U B).trace =
      (tokenDimension C : ℂ) * ((canonicalEncoding mu C U A)ᴴ * B).trace) ∧
    (∫ g, overlapWeight C g ∂mu) = 1 ∧
    (∀ g h, overlapWeight C (h * g * h⁻¹) = overlapWeight C g) ∧
    (∀ h rho, IsDensityMatrix rho →
      effectiveChannel mu C U (conjSuperop (repMatrix U h) rho) =
        conjSuperop (repMatrix U h) (effectiveChannel mu C U rho)) ∧
    (∀ outcome rho, IsDensityMatrix rho →
      (tokenDimension C : ℂ) • (∫ g,
        (Complex.normSq (∑ a, conj (tokenOrbit C outcome a) * tokenOrbit C g a) : ℂ) •
          conjSuperop (repMatrix U (outcome⁻¹ * g)) rho ∂mu) =
        effectiveChannel mu C U rho) ∧
    (∀ rho, IsDensityMatrix rho →
      canonicalRecovery mu C U (canonicalEncoding mu C U rho) = effectiveChannel mu C U rho) := by sorry

end GeneralResults

end QAlgorithms.Papers.Independent.Next46.P29

end
