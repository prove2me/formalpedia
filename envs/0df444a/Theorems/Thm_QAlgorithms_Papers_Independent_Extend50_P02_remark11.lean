-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P02_remark11
-- name    : QAlgorithms.Papers.Independent.Extend50.P02.remark11
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:46:14.628371+00:00
-- url     : https://prove2.me/theorems/99e4797f-56d5-4ad1-a49c-1d8d373576d7
-- title:
--   remark-11-two-extendible-SDP
-- statement:
--   All registers are nonzero finite-dimensional complex Hilbert spaces with fixed computational bases. States are positive semidefinite with trace one, and every resource or target channel is completely positive and trace preserving (CPTP). Write $\Gamma(\mathcal N)$ for the unnormalized, input-first Choi operator, so $\operatorname{Tr}_{\mathrm{out}}\Gamma(\mathcal N)=I_{\mathrm{in}}$. Every operator inequality is in Loewner order, and all transposes use the fixed product bases.
--
--   For channels $\mathcal O,\mathcal S:A\to B$, let $D(\mathcal O,\mathcal S)=\tfrac12\|\mathcal O-\mathcal S\|_\diamond$ and let $F_{\rm wc}(\mathcal O,\mathcal S)$ be the infimum of squared Uhlmann fidelity over normalized reference-assisted inputs. Thus the two errors are $D$ and $1-F_{\rm wc}$. For an assistance class $\mathsf C$, $e_{\mathsf C}^D$ and $e_{\mathsf C}^F$ denote the respective infima over protocols in that class; the protocol is fixed independently of the unknown input. One-way LOCC ($\mathsf{1WL}$) means Alice instruments followed by Bob's conditional CPTP maps. LOCR means a probability mixture of product CPTP maps.
--
--   Let $\mathcal N:\widehat A\to\widehat B$ be the fixed resource channel. A correction superchannel has a bipartite CPTP representative $\mathcal P:A\widehat B\to\widehat A B$, non-signaling from Bob to Alice, and induces $\Gamma(\mathcal S)=\operatorname{Tr}_{\widehat A\widehat B}[\Gamma(\mathcal N)^T\Gamma(\mathcal P)]$, with canonical identity embeddings. Product assistance is one CPTP encoder and one CPTP decoder; LOCR allows shared randomness, and $\mathsf{1WL}$ allows an encoder instrument with a conditional decoder. The class $\mathsf{2PENS}$ has a symmetric two-Bob CPTP extension with exact marginal, PPT on Alice and on the second Bob, and additional non-signaling from Alice to both Bobs at the level of the extension. The class $\mathsf{2E}$ omits PPT and that additional NS condition.
--
--   Identify $A$ and $B$ by their computational bases and put $d=\dim A\ge2$, $a=\dim\widehat A$, $b=\dim\widehat B$, and $r=\sqrt{d^2-1}$. Each of the six variables $M^+,M^-,M^0,M^1,M^2,M^3$ acts on $\widehat A\widehat B_1\widehat B_2$. Write $\mathcal F$ for conjugation by the swap of $\widehat B_1,\widehat B_2$, $T_a$ for partial transpose on $\widehat A$, and $T_{ab}$ for partial transpose on $\widehat A\widehat B_1$. Define
--   $$
--   \mathcal B(X_0,X_1,X_2,X_3)=\begin{pmatrix}X_0+X_3&X_1-iX_2\\X_1+iX_2&X_0-X_3\end{pmatrix},\qquad
--   P=\frac{dM^0+M^1+rM^2}{2d},\quad
--   Q=\frac{2d(M^++M^-)+dM^0-M^1-rM^2}{2d}.
--   $$
--   Let $\mathsf D(X)$ mean $X=(\operatorname{Tr}_{\widehat B_2}X)\otimes I_{\widehat B_2}/b$. The common positivity and symmetry conditions are $M^+,M^-,M^0\ge0$, $\mathcal B(M^0,M^1,M^2,M^3)\ge0$, $\mathcal F(M^i)=M^i$ for $i\in\{+,-,0,1\}$, and $\mathcal F(M^i)=-M^i$ for $i\in\{2,3\}$. The block condition also forces $M^1,M^2,M^3$ to be Hermitian. For $d=2$ set $M^-=0$.
--
--   For an operator $X$ on $\widehat A\widehat B_1$ define the objective
--   $$
--   J(X,M)=\frac1b\operatorname{Re}\operatorname{Tr}[(X^T\otimes I_{\widehat B_2})P].
--   $$
--   All matrices have orders $ab^2$ or $2ab^2$, independent of the target dimension $d$; scalar coefficients may depend on $d$.
--
--   Let $\mathcal C_d^{2E}$ impose the common positivity and swap conditions, $\operatorname{Tr}_{\widehat A}(M^++M^-+M^0)=I$, and both $\mathsf D(P)$ and $\mathsf D(Q)$, with $M^-=0$ at $d=2$. Then
--   $$
--   e_{\mathsf{2E}}^D(\mathcal N)=1-\sup_{M\in\mathcal C_d^{2E}}J(\Gamma(\mathcal N),M).
--   $$
--   Neither PPT nor the extra Alice-to-both-Bobs NS equalities is imposed. The constructed definitions of $P,Q$ are retained even though the source abbreviates its range as (187)–(193).
-- source:
--   Quantifying the performance of approximate teleportation and quantum error correction via symmetric two-PPT-extendibility, arXiv:2207.06931v4, PDF p. 15, remark-11-two-extendible-SDP

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P02

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Extend50.P02

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (choi fromChoi)

variable {A B C D H J : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype H] [Fintype J]

/-- PDF p.15, Remark 11: (187)–(193), using constructed P,Q from (194)–(195).
This program imposes neither PPT nor extra Alice-to-both-Bobs NS. -/
theorem remark11 [Nonempty A] [Nonempty H] [Nonempty J]
    (hd : 2 ≤ Fintype.card A) (N : Superop H J) (hN : IsChannel N) :
    correctionError .diamond (.extendible false false) (id : Superop A A) N =
      reducedCorrectionBound false false (Fintype.card A) N := by sorry

end QAlgorithms.Papers.Independent.Extend50.P02

end
