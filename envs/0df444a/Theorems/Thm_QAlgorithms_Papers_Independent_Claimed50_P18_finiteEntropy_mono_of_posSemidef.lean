-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_finiteEntropy_mono_of_posSemidef
-- name    : QAlgorithms.Papers.Independent.Claimed50.P18.finiteEntropy_mono_of_posSemidef
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-03T22:43:34.233375+00:00
-- url     : https://prove2.me/theorems/8a395480-7c6c-4e84-acc5-430a65718eb3
-- title:
--   Homogeneous entropy is monotone in the Loewner order
-- statement:
--   Throughout, for a finite index type $n$ and $X\in M_n(\mathbb C)$, $H(X)$ denotes the frozen `finiteEntropy` of Frontier18.P01, the homogeneous entropy $H(X)=\max\bigl(0,\,-\operatorname{Tr}\eta(X)+\operatorname{Tr}X\,\log\operatorname{Tr}X\bigr)\in[0,\infty)$ with $\eta(x)=x\log x$ applied by the continuous functional calculus (natural logarithms, $0\log 0=0$). For a positive semidefinite $X\ne0$ this is $\operatorname{Tr}X\cdot S(X/\operatorname{Tr}X)$, with $S$ the von Neumann entropy, and $H(0)=0$. Let $X,Y\in M_n(\mathbb C)$ with $0\le X\le Y$ in the Loewner order ($X$ and $Y-X$ positive semidefinite). Then
--
--   $$
--   H(X)\le H(Y).
--   $$
--
--   Reason: $H$ is the perspective $X\mapsto\operatorname{Tr}X\cdot S(X/\operatorname{Tr}X)$ of the concave von Neumann entropy, so it is concave and positively homogeneous of degree one on the positive cone, hence superadditive, $H(X+Z)\ge H(X)+H(Z)\ge H(X)$ for $Z=Y-X\ge0$.
-- source:
--   Kuznetsova, Quantum conditional entropy for infinite-dimensional systems, arXiv:1004.4519v2, PDF p. 2, §1 (step H(AB)=H(C) for pure rho_ABC); Lindblad, Commun. Math. Phys. 39 (1974) 111-119 (homogeneous entropy, Lemma 1 compression limit); Wehrl, Rev. Mod. Phys. 50 (1978) 221, §II.B (concavity, continuity of entropy in finite dimensions)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P18

noncomputable section

open Filter

open scoped ENNReal BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01

open QAlgorithms.Papers.Independent.Frontier18.P08 (operatorTrace)

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P18

open scoped Matrix ComplexOrder

theorem finiteEntropy_mono_of_posSemidef {n : Type} [Fintype n] [DecidableEq n]
    {X Y : Matrix n n ℂ} (hX : X.PosSemidef) (hXY : (Y - X).PosSemidef) :
    finiteEntropy X ≤ finiteEntropy Y := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P18

end
