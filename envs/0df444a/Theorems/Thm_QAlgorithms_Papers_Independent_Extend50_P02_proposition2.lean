-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P02_proposition2
-- name    : QAlgorithms.Papers.Independent.Extend50.P02.proposition2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:36:56.689344+00:00
-- url     : https://prove2.me/theorems/e7041239-d993-490c-bdcb-efbd97e57aae
-- title:
--   proposition-2
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces with fixed computational bases. States are positive semidefinite with trace one, and every resource or target channel is completely positive and trace preserving (CPTP). Write $\Gamma(\mathcal N)$ for the unnormalized, input-first Choi operator, so $\operatorname{Tr}_{\mathrm{out}}\Gamma(\mathcal N)=I_{\mathrm{in}}$. Every operator inequality is in Loewner order, and all transposes use the fixed product bases.
--
--   For channels $\mathcal O,\mathcal S:A\to B$, let $D(\mathcal O,\mathcal S)=\tfrac12\|\mathcal O-\mathcal S\|_\diamond$ and let $F_{\rm wc}(\mathcal O,\mathcal S)$ be the infimum of squared Uhlmann fidelity over normalized reference-assisted inputs. Thus the two errors are $D$ and $1-F_{\rm wc}$. For an assistance class $\mathsf C$, $e_{\mathsf C}^D$ and $e_{\mathsf C}^F$ denote the respective infima over protocols in that class; the protocol is fixed independently of the unknown input. One-way LOCC ($\mathsf{1WL}$) means Alice instruments followed by Bob's conditional CPTP maps. LOCR means a probability mixture of product CPTP maps.
--
--   For a fixed state $\rho_{\widehat A\widehat B}$, a teleportation protocol $\mathcal L:A\widehat A\widehat B\to B$ induces $\mathcal S(X)=\mathcal L(X\otimes\rho)$. The superscript-free $e_{\mathsf C}$ means $e_{\mathsf C}^D$. The class $\mathsf{2PE}$ consists of channels with a symmetric two-Bob CPTP extension, an exact non-signaling marginal, and positive partial transposes on Alice's registers and on the second Bob's registers. The class $\mathsf{2E}$ retains the extension conditions and omits PPT. Let $\mathcal N:A\to B$ be an arbitrary target channel, allowing different input and output dimensions. Put $b=\dim\widehat B$. Optimize over $\mu\ge0$, $Z_{AB}\ge0$, and $M\ge0$, where $M$ is the Choi operator of $A\widehat A\widehat B_1\widehat B_2\to B_1B_2$. Let $W=\operatorname{Tr}_{\widehat B_2B_2}M/b$, retaining $A\widehat A\widehat B_1B_1$, and put $C=\operatorname{Tr}_{\widehat A\widehat B_1}[(\rho^T\otimes I)W]$. Then
--   $$
--   e_{\mathsf{2PE}}(\mathcal N,\rho)=\inf\mu
--   $$
--   subject to $\mu I_A\ge\operatorname{Tr}_B Z$, $Z\ge\Gamma(\mathcal N)-C$, $\operatorname{Tr}_{B_1B_2}M=I_{A\widehat A\widehat B_1\widehat B_2}$, simultaneous Bob input/output swap invariance, $\operatorname{Tr}_{B_2}M=W\otimes I_{\widehat B_2}$ with the canonical register order, $T_{A\widehat A}M\ge0$, and $T_{\widehat B_2B_2}M\ge0$. This gives the exact unreduced SDP for the relaxation.
-- source:
--   Quantifying the performance of approximate teleportation and quantum error correction via symmetric two-PPT-extendibility, arXiv:2207.06931v4, PDF p. 8, proposition-2

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P02

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Extend50.P02

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (choi fromChoi)

variable {A B C D H J : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype H] [Fintype J]

/-- PDF pp.8–9, Proposition 2, (79)–(86): general target A->B;
M's marginal is a computed partial trace. A and B may have different dimensions. -/
theorem proposition2 [Nonempty A] [Nonempty B] [Nonempty H] [Nonempty J]
    (N : Superop A B) (hN : IsChannel N)
    (rho : Op (H × J)) (hrho : IsDensityMatrix rho) :
    teleportError .diamond (some true) N rho =
      sInf {mu : ℝ | ∃ Z : Op (A × B), ∃ M : ExtOp (A × H) J Unit B,
        TeleportSDP N rho mu Z M} := by sorry

end QAlgorithms.Papers.Independent.Extend50.P02

end
