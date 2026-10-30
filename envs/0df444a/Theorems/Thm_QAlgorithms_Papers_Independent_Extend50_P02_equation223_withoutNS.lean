-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P02_equation223_withoutNS
-- name    : QAlgorithms.Papers.Independent.Extend50.P02.equation223_withoutNS
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:48:51.660995+00:00
-- url     : https://prove2.me/theorems/9c266bb9-4269-4bff-92b4-5fec341ac734
-- title:
--   equation-223-without-NS
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces with fixed computational bases. States are positive semidefinite with trace one, and every resource or target channel is completely positive and trace preserving (CPTP). Write $\Gamma(\mathcal N)$ for the unnormalized, input-first Choi operator, so $\operatorname{Tr}_{\mathrm{out}}\Gamma(\mathcal N)=I_{\mathrm{in}}$. Every operator inequality is in Loewner order, and all transposes use the fixed product bases.
--
--   For channels $\mathcal O,\mathcal S:A\to B$, let $D(\mathcal O,\mathcal S)=\tfrac12\|\mathcal O-\mathcal S\|_\diamond$ and let $F_{\rm wc}(\mathcal O,\mathcal S)$ be the infimum of squared Uhlmann fidelity over normalized reference-assisted inputs. Thus the two errors are $D$ and $1-F_{\rm wc}$. For an assistance class $\mathsf C$, $e_{\mathsf C}^D$ and $e_{\mathsf C}^F$ denote the respective infima over protocols in that class; the protocol is fixed independently of the unknown input. One-way LOCC ($\mathsf{1WL}$) means Alice instruments followed by Bob's conditional CPTP maps. LOCR means a probability mixture of product CPTP maps.
--
--   Let $\mathcal N:\widehat A\to\widehat B$ be the fixed resource channel. A correction superchannel has a bipartite CPTP representative $\mathcal P:A\widehat B\to\widehat A B$, non-signaling from Bob to Alice, and induces $\Gamma(\mathcal S)=\operatorname{Tr}_{\widehat A\widehat B}[\Gamma(\mathcal N)^T\Gamma(\mathcal P)]$, with canonical identity embeddings. Product assistance is one CPTP encoder and one CPTP decoder; LOCR allows shared randomness, and $\mathsf{1WL}$ allows an encoder instrument with a conditional decoder. The class $\mathsf{2PENS}$ has a symmetric two-Bob CPTP extension with exact marginal, PPT on Alice and on the second Bob, and additional non-signaling from Alice to both Bobs at the level of the extension. The class $\mathsf{2E}$ omits PPT and that additional NS condition.
--
--   For the identity target of dimension $d\ge2$, define
--   $$
--   b_{\rm PPTNS}(\mathcal N)=1-\sup_{K,\sigma}\operatorname{Re}\operatorname{Tr}[K\Gamma(\mathcal N)]
--   $$
--   over $K\ge0$, $\sigma\ge0$, $\operatorname{Tr}\sigma=1$, $K\le\sigma\otimes I_{\widehat B}$, $\sigma\otimes I_{\widehat B}\pm dT_{\widehat B}(K)\ge0$, and $d^2\operatorname{Tr}_{\widehat A}K=I_{\widehat B}$. Remove exactly the equality $d^2\operatorname{Tr}_{\widehat A}K=I_{\widehat B}$ and call the resulting value $b_{\rm PPT}(\mathcal N)$. Then
--   $$
--   b_{\rm PPT}(\mathcal N)\le e_{\mathsf{1WL}}^D(\mathcal N),\qquad
--   b_{\rm PPT}(\mathcal N)\le e_{\mathsf{1WL}}^F(\mathcal N).
--   $$
--   The trace-one condition on $\sigma$, positivity, and the inherent superchannel causality condition remain. This is the one-way-assisted correction relaxation described after (223).
-- source:
--   Quantifying the performance of approximate teleportation and quantum error correction via symmetric two-PPT-extendibility, arXiv:2207.06931v4, PDF p. 17, equation-223-without-NS

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P02

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Extend50.P02

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (choi fromChoi)

variable {A B C D H J : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype H] [Fintype J]

/-- PDF p.17, paragraph after (223): remove exactly d^2 Tr_H K=I_J;
retain sigma's trace normalization, positivity, and the causal superchannel condition. -/
theorem equation223_withoutNS [Nonempty A] [Nonempty H] [Nonempty J]
    (hd : 2 ≤ Fintype.card A) (N : Superop H J) (hN : IsChannel N) :
    ∀ c : Criterion, pptCorrectionBound false (Fintype.card A) N ≤
      correctionError c .oneWay (id : Superop A A) N := by sorry

end QAlgorithms.Papers.Independent.Extend50.P02

end
