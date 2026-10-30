-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P02_proposition9
-- name    : QAlgorithms.Papers.Independent.Extend50.P02.proposition9
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:41:26.335916+00:00
-- url     : https://prove2.me/theorems/787c25c0-07f1-4d3c-a040-e7369750995b
-- title:
--   proposition-9
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
--   The additional reduced NS constraints $\mathsf N_d(M)$ are
--   $$
--   \begin{aligned}
--   &\frac{\operatorname{Tr}_{\widehat A}(2M^+)}{(d+2)(d-1)}=\frac{\operatorname{Tr}_{\widehat A}(2M^++M^0+M^1)}{d(d+1)},\\
--   &\frac12\operatorname{Tr}_{\widehat A}M^0=\frac{dI+\operatorname{Tr}_{\widehat A}(M^--M^+-M^1)}{d(d^2-1)},\\
--   &\frac12\operatorname{Tr}_{\widehat A}M^1=\frac{-I+d\operatorname{Tr}_{\widehat A}(M^+-M^-+M^1)}{d(d^2-1)},\\
--   &\operatorname{Tr}_{\widehat A}M^2=\operatorname{Tr}_{\widehat A}M^3=0.
--   \end{aligned}
--   $$
--   For $d\ge3$ also require
--   $$
--   \frac{\operatorname{Tr}_{\widehat A}(2M^-)}{(d-2)(d+1)}=\frac{\operatorname{Tr}_{\widehat A}(2M^-+M^0-M^1)}{d(d-1)}.
--   $$
--   This last equality is omitted at $d=2$; every identity here acts on $\widehat B_1\widehat B_2$.
--
--   Let $\mathcal C_d$ consist of the common conditions, $\operatorname{Tr}_{\widehat A}(M^++M^-+M^0)=I$, both $\mathsf D(P)$ and $\mathsf D(Q)$, $\mathsf P_d(M)$, and $\mathsf N_d(M)$. Then
--   $$
--   e_{\mathsf{2PENS}}^D(\mathcal N)=e_{\mathsf{2PENS}}^F(\mathcal N)=1-\sup_{M\in\mathcal C_d}J(\Gamma(\mathcal N),M).
--   $$
--   At $d=2$ omit (197), (204), and (214), as encoded above. This retains the extra non-signaling condition on the full extension.
-- source:
--   Quantifying the performance of approximate teleportation and quantum error correction via symmetric two-PPT-extendibility, arXiv:2207.06931v4, PDF p. 14, proposition-9

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P02

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Extend50.P02

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (choi fromChoi)

variable {A B C D H J : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype H] [Fintype J]

/-- PDF pp.14–15, Proposition 9, (186)–(217): full reduced 2PENS program,
with both P and Q marginal constraints, all extra NS equalities, and the d=2 case. -/
theorem proposition9 [Nonempty A] [Nonempty H] [Nonempty J]
    (hd : 2 ≤ Fintype.card A) (N : Superop H J) (hN : IsChannel N) :
    correctionError .diamond (.extendible true true) (id : Superop A A) N =
      correctionError .infidelity (.extendible true true) (id : Superop A A) N ∧
    correctionError .diamond (.extendible true true) (id : Superop A A) N =
      reducedCorrectionBound true true (Fintype.card A) N := by sorry

end QAlgorithms.Papers.Independent.Extend50.P02

end
