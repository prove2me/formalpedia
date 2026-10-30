-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P02_equation78
-- name    : QAlgorithms.Papers.Independent.Extend50.P02.equation78
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:43:05.432453+00:00
-- url     : https://prove2.me/theorems/2575c2f2-cfea-4735-9e89-a25d83616aba
-- title:
--   equation-78
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces with fixed computational bases. States are positive semidefinite with trace one, and every resource or target channel is completely positive and trace preserving (CPTP). Write $\Gamma(\mathcal N)$ for the unnormalized, input-first Choi operator, so $\operatorname{Tr}_{\mathrm{out}}\Gamma(\mathcal N)=I_{\mathrm{in}}$. Every operator inequality is in Loewner order, and all transposes use the fixed product bases.
--
--   For channels $\mathcal O,\mathcal S:A\to B$, let $D(\mathcal O,\mathcal S)=\tfrac12\|\mathcal O-\mathcal S\|_\diamond$ and let $F_{\rm wc}(\mathcal O,\mathcal S)$ be the infimum of squared Uhlmann fidelity over normalized reference-assisted inputs. Thus the two errors are $D$ and $1-F_{\rm wc}$. For an assistance class $\mathsf C$, $e_{\mathsf C}^D$ and $e_{\mathsf C}^F$ denote the respective infima over protocols in that class; the protocol is fixed independently of the unknown input. One-way LOCC ($\mathsf{1WL}$) means Alice instruments followed by Bob's conditional CPTP maps. LOCR means a probability mixture of product CPTP maps.
--
--   For a fixed state $\rho_{\widehat A\widehat B}$, a teleportation protocol $\mathcal L:A\widehat A\widehat B\to B$ induces $\mathcal S(X)=\mathcal L(X\otimes\rho)$. The superscript-free $e_{\mathsf C}$ means $e_{\mathsf C}^D$. The class $\mathsf{2PE}$ consists of channels with a symmetric two-Bob CPTP extension, an exact non-signaling marginal, and positive partial transposes on Alice's registers and on the second Bob's registers. The class $\mathsf{2E}$ retains the extension conditions and omits PPT. For every CPTP target $\mathcal N:A\to B$ and every resource state $\rho$,
--   $$
--   e_{\mathsf{2PE}}^D(\mathcal N,\rho)\le e_{\mathsf{1WL}}^D(\mathcal N,\rho).
--   $$
--   This is a weak lower bound arising from inclusion of the protocol classes; it includes singleton registers and asserts no uniform strictness.
-- source:
--   Quantifying the performance of approximate teleportation and quantum error correction via symmetric two-PPT-extendibility, arXiv:2207.06931v4, PDF p. 8, equation-78

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P02

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Extend50.P02

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (choi fromChoi)

variable {A B C D H J : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype H] [Fintype J]

/-- PDF p.8, (78): weak lower bound for any target, including singleton registers. -/
theorem equation78 [Nonempty A] [Nonempty B] [Nonempty H] [Nonempty J]
    (N : Superop A B) (hN : IsChannel N)
    (rho : Op (H × J)) (hrho : IsDensityMatrix rho) :
    teleportError .diamond (some true) N rho ≤ teleportError .diamond none N rho := by sorry

end QAlgorithms.Papers.Independent.Extend50.P02

end
