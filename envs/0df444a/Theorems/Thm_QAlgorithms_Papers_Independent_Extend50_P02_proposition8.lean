-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P02_proposition8
-- name    : QAlgorithms.Papers.Independent.Extend50.P02.proposition8
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:40:32.14869+00:00
-- url     : https://prove2.me/theorems/08d165bc-94d2-4357-ac55-4367be81852c
-- title:
--   proposition-8
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces with fixed computational bases. States are positive semidefinite with trace one, and every resource or target channel is completely positive and trace preserving (CPTP). Write $\Gamma(\mathcal N)$ for the unnormalized, input-first Choi operator, so $\operatorname{Tr}_{\mathrm{out}}\Gamma(\mathcal N)=I_{\mathrm{in}}$. Every operator inequality is in Loewner order, and all transposes use the fixed product bases.
--
--   For channels $\mathcal O,\mathcal S:A\to B$, let $D(\mathcal O,\mathcal S)=\tfrac12\|\mathcal O-\mathcal S\|_\diamond$ and let $F_{\rm wc}(\mathcal O,\mathcal S)$ be the infimum of squared Uhlmann fidelity over normalized reference-assisted inputs. Thus the two errors are $D$ and $1-F_{\rm wc}$. For an assistance class $\mathsf C$, $e_{\mathsf C}^D$ and $e_{\mathsf C}^F$ denote the respective infima over protocols in that class; the protocol is fixed independently of the unknown input. One-way LOCC ($\mathsf{1WL}$) means Alice instruments followed by Bob's conditional CPTP maps. LOCR means a probability mixture of product CPTP maps.
--
--   Let $\mathcal N:\widehat A\to\widehat B$ be the fixed resource channel. A correction superchannel has a bipartite CPTP representative $\mathcal P:A\widehat B\to\widehat A B$, non-signaling from Bob to Alice, and induces $\Gamma(\mathcal S)=\operatorname{Tr}_{\widehat A\widehat B}[\Gamma(\mathcal N)^T\Gamma(\mathcal P)]$, with canonical identity embeddings. Product assistance is one CPTP encoder and one CPTP decoder; LOCR allows shared randomness, and $\mathsf{1WL}$ allows an encoder instrument with a conditional decoder. The class $\mathsf{2PENS}$ has a symmetric two-Bob CPTP extension with exact marginal, PPT on Alice and on the second Bob, and additional non-signaling from Alice to both Bobs at the level of the extension. The class $\mathsf{2E}$ omits PPT and that additional NS condition. Let $\mathcal O:A\to B$ be an arbitrary CPTP target. Write $b=\dim\widehat B$. Optimize over $\mu\ge0$, $Z_{AB}\ge0$, and $M\ge0$, where $M$ is the Choi operator of $A\widehat B_1\widehat B_2\to\widehat A B_1B_2$. Put $W=\operatorname{Tr}_{\widehat B_2B_2}M/b$ and $C=\operatorname{Tr}_{\widehat A\widehat B_1}[(\Gamma(\mathcal N)^T\otimes I)W]$. Then
--   $$
--   e_{\mathsf{2PENS}}(\mathcal O,\mathcal N)=\inf\mu
--   $$
--   subject to $\mu I_A\ge\operatorname{Tr}_B Z$, $Z\ge\Gamma(\mathcal O)-C$, $\operatorname{Tr}_{\widehat A B_1B_2}M=I_{A\widehat B_1\widehat B_2}$, simultaneous Bob input/output swap invariance, $\operatorname{Tr}_{B_2}M=W\otimes I_{\widehat B_2}$, $T_{A\widehat A}M\ge0$, $T_{\widehat B_2B_2}M\ge0$, and
--   $$
--   \operatorname{Tr}_{\widehat A}M=\frac{I_A}{\dim A}\otimes\operatorname{Tr}_{A\widehat A}M.
--   $$
--   All partial traces retain every untraced register and tensor factors are put in the fixed register order. This is the exact unreduced error-correction SDP.
-- source:
--   Quantifying the performance of approximate teleportation and quantum error correction via symmetric two-PPT-extendibility, arXiv:2207.06931v4, PDF p. 14, proposition-8

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P02

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Extend50.P02

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (choi fromChoi)

variable {A B C D H J : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype H] [Fintype J]

/-- PDF p.14, Proposition 8, (175)–(183): general target O and resource N;
the extension is A J1 J2 -> H B1 B2 and carries the extra NS constraint. -/
theorem proposition8 [Nonempty A] [Nonempty B] [Nonempty H] [Nonempty J]
    (O : Superop A B) (hO : IsChannel O) (N : Superop H J) (hN : IsChannel N) :
    correctionError .diamond (.extendible true true) O N =
      sInf {mu : ℝ | ∃ Z : Op (A × B), ∃ M : ExtOp A J H B,
        CorrectionSDP O N mu Z M} := by sorry

end QAlgorithms.Papers.Independent.Extend50.P02

end
