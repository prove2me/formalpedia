-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P02_equation220
-- name    : QAlgorithms.Papers.Independent.Extend50.P02.equation220
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:47:36.583996+00:00
-- url     : https://prove2.me/theorems/99f66378-5578-4271-8f7e-cfd19fbfa143
-- title:
--   equation-220
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces with fixed computational bases. States are positive semidefinite with trace one, and every resource or target channel is completely positive and trace preserving (CPTP). Write $\Gamma(\mathcal N)$ for the unnormalized, input-first Choi operator, so $\operatorname{Tr}_{\mathrm{out}}\Gamma(\mathcal N)=I_{\mathrm{in}}$. Every operator inequality is in Loewner order, and all transposes use the fixed product bases.
--
--   For channels $\mathcal O,\mathcal S:A\to B$, let $D(\mathcal O,\mathcal S)=\tfrac12\|\mathcal O-\mathcal S\|_\diamond$ and let $F_{\rm wc}(\mathcal O,\mathcal S)$ be the infimum of squared Uhlmann fidelity over normalized reference-assisted inputs. Thus the two errors are $D$ and $1-F_{\rm wc}$. For an assistance class $\mathsf C$, $e_{\mathsf C}^D$ and $e_{\mathsf C}^F$ denote the respective infima over protocols in that class; the protocol is fixed independently of the unknown input. One-way LOCC ($\mathsf{1WL}$) means Alice instruments followed by Bob's conditional CPTP maps. LOCR means a probability mixture of product CPTP maps.
--
--   For a fixed state $\rho_{\widehat A\widehat B}$, a teleportation protocol $\mathcal L:A\widehat A\widehat B\to B$ induces $\mathcal S(X)=\mathcal L(X\otimes\rho)$. The superscript-free $e_{\mathsf C}$ means $e_{\mathsf C}^D$. The class $\mathsf{2PE}$ consists of channels with a symmetric two-Bob CPTP extension, an exact non-signaling marginal, and positive partial transposes on Alice's registers and on the second Bob's registers. The class $\mathsf{2E}$ retains the extension conditions and omits PPT. For the target identity of dimension $d\ge2$, define
--   $$
--   b_{\rm PPT}(\rho)=1-\sup\{\operatorname{Tr}(K\rho):0\le K\le I,\ -I\le dT_{\widehat B}(K)\le I\}.
--   $$
--   Then
--   $$
--   b_{\rm PPT}(\rho)\le e_{\mathsf{2PE}}^D(\rho),\qquad
--   b_{\rm PPT}(\rho)\le e_{\mathsf{1WL}}^D(\rho),\quad
--   b_{\rm PPT}(\rho)\le e_{\mathsf{1WL}}^F(\rho).
--   $$
--   This expresses (220) as an operational error lower bound. The first comparison corrects the reversed error-order wording on p.16; the relevant teleportation program is (90), not the channel program (187).
-- source:
--   Quantifying the performance of approximate teleportation and quantum error correction via symmetric two-PPT-extendibility, arXiv:2207.06931v4, PDF p. 16, equation-220

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P02

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Extend50.P02

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (choi fromChoi)

variable {A B C D H J : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype H] [Fintype J]

/-- PDF p.16, (220), Appendix F pp.44–46: PPT-only lower bound for both criteria.
SOURCE CORRECTION: p.16 prints "not smaller" and references (187). The feasible-set
argument gives PPT bound <= two-PPT-extendible teleportation error, whose formula
is (90). We state that direction; independent source moderation is pending. -/
theorem equation220 [Nonempty A] [Nonempty H] [Nonempty J]
    (hd : 2 ≤ Fintype.card A) (rho : Op (H × J)) (hrho : IsDensityMatrix rho) :
    pptTeleportBound (Fintype.card A) rho ≤
      teleportError .diamond (some true) (id : Superop A A) rho ∧
    (∀ c : Criterion, pptTeleportBound (Fintype.card A) rho ≤
      teleportError c none (id : Superop A A) rho) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P02

end
