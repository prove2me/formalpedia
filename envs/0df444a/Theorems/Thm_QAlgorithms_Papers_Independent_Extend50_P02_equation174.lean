-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P02_equation174
-- name    : QAlgorithms.Papers.Independent.Extend50.P02.equation174
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:43:43.98676+00:00
-- url     : https://prove2.me/theorems/1285fd12-687c-4ea1-a55e-cab4ecf78922
-- title:
--   equation-174
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces with fixed computational bases. States are positive semidefinite with trace one, and every resource or target channel is completely positive and trace preserving (CPTP). Write $\Gamma(\mathcal N)$ for the unnormalized, input-first Choi operator, so $\operatorname{Tr}_{\mathrm{out}}\Gamma(\mathcal N)=I_{\mathrm{in}}$. Every operator inequality is in Loewner order, and all transposes use the fixed product bases.
--
--   For channels $\mathcal O,\mathcal S:A\to B$, let $D(\mathcal O,\mathcal S)=\tfrac12\|\mathcal O-\mathcal S\|_\diamond$ and let $F_{\rm wc}(\mathcal O,\mathcal S)$ be the infimum of squared Uhlmann fidelity over normalized reference-assisted inputs. Thus the two errors are $D$ and $1-F_{\rm wc}$. For an assistance class $\mathsf C$, $e_{\mathsf C}^D$ and $e_{\mathsf C}^F$ denote the respective infima over protocols in that class; the protocol is fixed independently of the unknown input. One-way LOCC ($\mathsf{1WL}$) means Alice instruments followed by Bob's conditional CPTP maps. LOCR means a probability mixture of product CPTP maps.
--
--   Let $\mathcal N:\widehat A\to\widehat B$ be the fixed resource channel. A correction superchannel has a bipartite CPTP representative $\mathcal P:A\widehat B\to\widehat A B$, non-signaling from Bob to Alice, and induces $\Gamma(\mathcal S)=\operatorname{Tr}_{\widehat A\widehat B}[\Gamma(\mathcal N)^T\Gamma(\mathcal P)]$, with canonical identity embeddings. Product assistance is one CPTP encoder and one CPTP decoder; LOCR allows shared randomness, and $\mathsf{1WL}$ allows an encoder instrument with a conditional decoder. The class $\mathsf{2PENS}$ has a symmetric two-Bob CPTP extension with exact marginal, PPT on Alice and on the second Bob, and additional non-signaling from Alice to both Bobs at the level of the extension. The class $\mathsf{2E}$ omits PPT and that additional NS condition. For every CPTP target $\mathcal O:A\to B$,
--   $$
--   e_{\mathsf{2PENS}}^D(\mathcal O,\mathcal N)\le e_{\mathrm{LOCR}}^D(\mathcal O,\mathcal N).
--   $$
--   This relaxation is justified by LOCR inclusion. It does not assert that arbitrary one-way instruments satisfy the extra Alice-to-both-Bobs non-signaling condition.
-- source:
--   Quantifying the performance of approximate teleportation and quantum error correction via symmetric two-PPT-extendibility, arXiv:2207.06931v4, PDF p. 14, equation-174

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P02

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Extend50.P02

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (choi fromChoi)

variable {A B C D H J : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype H] [Fintype J]

/-- PDF p.14, (174): LOCR is contained in 2PENS; no claim that all 1WL is in 2PENS. -/
theorem equation174 [Nonempty A] [Nonempty B] [Nonempty H] [Nonempty J]
    (O : Superop A B) (hO : IsChannel O) (N : Superop H J) (hN : IsChannel N) :
    correctionError .diamond (.extendible true true) O N ≤
      correctionError .diamond .locr O N := by sorry

end QAlgorithms.Papers.Independent.Extend50.P02

end
