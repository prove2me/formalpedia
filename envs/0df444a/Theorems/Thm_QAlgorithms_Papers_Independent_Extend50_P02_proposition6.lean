-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P02_proposition6
-- name    : QAlgorithms.Papers.Independent.Extend50.P02.proposition6
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:38:47.817096+00:00
-- url     : https://prove2.me/theorems/cb417b7a-a659-49c0-a4c2-b7aaa34bdc1f
-- title:
--   proposition-6
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces with fixed computational bases. States are positive semidefinite with trace one, and every resource or target channel is completely positive and trace preserving (CPTP). Write $\Gamma(\mathcal N)$ for the unnormalized, input-first Choi operator, so $\operatorname{Tr}_{\mathrm{out}}\Gamma(\mathcal N)=I_{\mathrm{in}}$. Every operator inequality is in Loewner order, and all transposes use the fixed product bases.
--
--   For channels $\mathcal O,\mathcal S:A\to B$, let $D(\mathcal O,\mathcal S)=\tfrac12\|\mathcal O-\mathcal S\|_\diamond$ and let $F_{\rm wc}(\mathcal O,\mathcal S)$ be the infimum of squared Uhlmann fidelity over normalized reference-assisted inputs. Thus the two errors are $D$ and $1-F_{\rm wc}$. For an assistance class $\mathsf C$, $e_{\mathsf C}^D$ and $e_{\mathsf C}^F$ denote the respective infima over protocols in that class; the protocol is fixed independently of the unknown input. One-way LOCC ($\mathsf{1WL}$) means Alice instruments followed by Bob's conditional CPTP maps. LOCR means a probability mixture of product CPTP maps.
--
--   Let $\mathcal N:\widehat A\to\widehat B$ be the fixed resource channel. A correction superchannel has a bipartite CPTP representative $\mathcal P:A\widehat B\to\widehat A B$, non-signaling from Bob to Alice, and induces $\Gamma(\mathcal S)=\operatorname{Tr}_{\widehat A\widehat B}[\Gamma(\mathcal N)^T\Gamma(\mathcal P)]$, with canonical identity embeddings. Product assistance is one CPTP encoder and one CPTP decoder; LOCR allows shared randomness, and $\mathsf{1WL}$ allows an encoder instrument with a conditional decoder. The class $\mathsf{2PENS}$ has a symmetric two-Bob CPTP extension with exact marginal, PPT on Alice and on the second Bob, and additional non-signaling from Alice to both Bobs at the level of the extension. The class $\mathsf{2E}$ omits PPT and that additional NS condition. For every positive target dimension $d$ and the identity target $\mathrm{id}_d$,
--   $$
--   e_{\mathrm{LOCR}}^D(\mathcal N)=e_{\mathrm{LOCR}}^F(\mathcal N).
--   $$
--   This equality concerns the optimizations with free common randomness, which makes twirling admissible.
-- source:
--   Quantifying the performance of approximate teleportation and quantum error correction via symmetric two-PPT-extendibility, arXiv:2207.06931v4, PDF p. 13, proposition-6

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P02

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Extend50.P02

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (choi fromChoi)

variable {A B C D H J : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype H] [Fintype J]

/-- PDF p.13, Proposition 6, (158): equality uses free common randomness. -/
theorem proposition6 [Nonempty A] [Nonempty H] [Nonempty J]
    (N : Superop H J) (hN : IsChannel N) :
    correctionError .diamond .locr (id : Superop A A) N =
      correctionError .infidelity .locr (id : Superop A A) N := by sorry

end QAlgorithms.Papers.Independent.Extend50.P02

end
