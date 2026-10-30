-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P02_proposition1
-- name    : QAlgorithms.Papers.Independent.Extend50.P02.proposition1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:36:10.56697+00:00
-- url     : https://prove2.me/theorems/cfbbb6c9-67c7-4af0-93cd-b17c92e15176
-- title:
--   proposition-1
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces with fixed computational bases. States are positive semidefinite with trace one, and every resource or target channel is completely positive and trace preserving (CPTP). Write $\Gamma(\mathcal N)$ for the unnormalized, input-first Choi operator, so $\operatorname{Tr}_{\mathrm{out}}\Gamma(\mathcal N)=I_{\mathrm{in}}$. Every operator inequality is in Loewner order, and all transposes use the fixed product bases.
--
--   For channels $\mathcal O,\mathcal S:A\to B$, let $D(\mathcal O,\mathcal S)=\tfrac12\|\mathcal O-\mathcal S\|_\diamond$ and let $F_{\rm wc}(\mathcal O,\mathcal S)$ be the infimum of squared Uhlmann fidelity over normalized reference-assisted inputs. Thus the two errors are $D$ and $1-F_{\rm wc}$. For an assistance class $\mathsf C$, $e_{\mathsf C}^D$ and $e_{\mathsf C}^F$ denote the respective infima over protocols in that class; the protocol is fixed independently of the unknown input. One-way LOCC ($\mathsf{1WL}$) means Alice instruments followed by Bob's conditional CPTP maps. LOCR means a probability mixture of product CPTP maps.
--
--   For a fixed state $\rho_{\widehat A\widehat B}$, a teleportation protocol $\mathcal L:A\widehat A\widehat B\to B$ induces $\mathcal S(X)=\mathcal L(X\otimes\rho)$. The superscript-free $e_{\mathsf C}$ means $e_{\mathsf C}^D$. The class $\mathsf{2PE}$ consists of channels with a symmetric two-Bob CPTP extension, an exact non-signaling marginal, and positive partial transposes on Alice's registers and on the second Bob's registers. The class $\mathsf{2E}$ retains the extension conditions and omits PPT. Identify $A=B$ with dimension $d\ge2$. Let $\mathcal D_d(X)=(d\operatorname{Tr}(X)I-X)/(d^2-1)$, the uniform nonidentity Weyl randomizing channel. For positive $K,L$ on $\widehat A\widehat B$ with $K+L=I$, construct
--   $$
--   \mathcal L_{K,L}(\omega)=\operatorname{Tr}_{\widehat A\widehat B}[(I_A\otimes K)\omega]+\mathcal D_d\!\left(\operatorname{Tr}_{\widehat A\widehat B}[(I_A\otimes L)\omega]\right).
--   $$
--   Then
--   $$
--   e_{\mathsf{1WL}}^D(\rho)=e_{\mathsf{1WL}}^F(\rho)=1-\sup_{\substack{K,L\ge0,\ K+L=I\\\mathcal L_{K,L}\in\mathsf{1WL}}}\operatorname{Tr}(K\rho).
--   $$
--   Furthermore, for every such $K,L$, membership $\mathcal L_{K,L}\in\mathsf{1WL}$ holds if and only if there exist a POVM $\{\Lambda_x\}$ on $B\widehat A$ and CPTP decoders $\mathcal D_x:\widehat B\to B$ such that
--   $$
--   K=\frac1{d^2}\sum_x\operatorname{Tr}_B[T_B(\Lambda_x)\Gamma(\mathcal D_x)].
--   $$
--   Products use the canonical embeddings on $B\widehat A\widehat B$. This identifies the full one-way optimization with a success-effect variational problem.
-- source:
--   Quantifying the performance of approximate teleportation and quantum error correction via symmetric two-PPT-extendibility, arXiv:2207.06931v4, PDF p. 8, proposition-1

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P02

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Extend50.P02

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (choi fromChoi)

variable {A B C D H J : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype H] [Fintype J]

/-- PDF p.8, Proposition 1, (66)–(70): both optimal errors, the full
variational formula, and the POVM/decoder iff. Requires nontrivial target d>=2. -/
theorem proposition1 [Nonempty A] [Nonempty H] [Nonempty J]
    (hd : 2 ≤ Fintype.card A) (rho : Op (H × J)) (hrho : IsDensityMatrix rho) :
    teleportError .diamond none (id : Superop A A) rho =
      teleportError .infidelity none (id : Superop A A) rho ∧
    teleportError .diamond none (id : Superop A A) rho =
      1 - teleportOneWaySuccess rho A ∧
    (∀ K L : Op (H × J), K.PosSemidef → L.PosSemidef → K + L = 1 →
      (IsAliceToBobLOCC (teleportBipartite (isotropicTeleport (A := A) K L)) ↔
        HasDecoderEffect K A)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P02

end
