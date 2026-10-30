-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P02_remark12
-- name    : QAlgorithms.Papers.Independent.Extend50.P02.remark12
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:47:03.771739+00:00
-- url     : https://prove2.me/theorems/251291ef-2a98-4b44-a332-7a05d424faa4
-- title:
--   remark-12
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
--   The PPT tests $\mathsf P_d(M)$ below are concrete constraints, not hypotheses assumed of a physical coefficient map. Define
--   $$
--   \begin{aligned}
--   &G_0=T_a(M^++M^-+(M^0-dM^1)/2),\quad G_1=T_a(M^+-M^-+(M^1-dM^0)/2),\\
--   &G_2=\tfrac12\sqrt{3(d^2-1)}\,T_a(M^2),\quad G_3=\tfrac12\sqrt{3(d^2-1)}\,T_a(M^3),\\
--   &L_0=(d^2-2)M^0+dM^1+drM^2,\quad L_1=dM^0+(2d^2-3)M^1-rM^2,\quad L_2=M^1-dM^0-rM^2,\\
--   &E_0=\frac{T_{ab}(d(M^+-M^-)+L_0/2)}{d^2-1},\quad E_1=\frac{T_{ab}(-M^++M^-+L_1/2)}{d^2-1},\\
--   &E_2=\frac{T_{ab}(M^+-M^-+L_2/2)}r,\quad E_3=T_{ab}(M^3).
--   \end{aligned}
--   $$
--   Require
--   $$
--   \begin{gathered}
--   T_a\!\left(\frac{2M^+}{d+2}+M^0+M^1\right)\ge0,\qquad
--   \mathcal B(G_0,G_1,G_2,G_3)\ge0,\qquad \mathcal B(E_0,E_1,E_2,E_3)\ge0,\\
--   T_{ab}\!\left(\frac{dM^+}{d+2}+M^-+\frac{dM^0-M^1-rM^2}{2}\right)\ge0.
--   \end{gathered}
--   $$
--   For $d\ge3$ also require
--   $$
--   T_a\!\left(\frac{2M^-}{d-2}+M^1-M^0\right)\ge0,\qquad
--   T_{ab}\!\left(M^++\frac{dM^-}{d-2}-\frac{dM^0-M^1-rM^2}{2}\right)\ge0.
--   $$
--   For $d=2$ omit these last two tests entirely.
--
--   Let $\mathcal C_d^{\rm no\ extra\ NS}$ impose the common conditions, $\operatorname{Tr}_{\widehat A}(M^++M^-+M^0)=I$, both $\mathsf D(P)$ and $\mathsf D(Q)$, and all $\mathsf P_d(M)$ tests, with the stated $d=2$ omissions. Then
--   $$
--   1-\sup_{M\in\mathcal C_d^{\rm no\ extra\ NS}}J(\Gamma(\mathcal N),M)
--   \le e_{\mathsf{1WL}}^D(\mathcal N)=e_{\mathsf{1WL}}^F(\mathcal N).
--   $$
--   Only (213)–(217) are removed; the different marginal NS constraints (192)–(193) remain. This bounds one-way-assisted correction and includes the equality stated on p.16.
-- source:
--   Quantifying the performance of approximate teleportation and quantum error correction via symmetric two-PPT-extendibility, arXiv:2207.06931v4, PDF p. 15, remark-12

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P02

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Extend50.P02

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (choi fromChoi)

variable {A B C D H J : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype H] [Fintype J]

/-- PDF pp.15–16, Remark 12: remove only (213)–(217), keep (192)–(193).
The reduced program lower-bounds one-way-assisted correction; its two optimal
operational error criteria coincide, as the continuation on p.16 states. -/
theorem remark12 [Nonempty A] [Nonempty H] [Nonempty J]
    (hd : 2 ≤ Fintype.card A) (N : Superop H J) (hN : IsChannel N) :
    reducedCorrectionBound true false (Fintype.card A) N ≤
      correctionError .diamond .oneWay (id : Superop A A) N ∧
    correctionError .diamond .oneWay (id : Superop A A) N =
      correctionError .infidelity .oneWay (id : Superop A A) N := by sorry

end QAlgorithms.Papers.Independent.Extend50.P02

end
