-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_finiteEntropy_tendsto
-- name    : QAlgorithms.Papers.Independent.Claimed50.P18.finiteEntropy_tendsto
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-03T22:43:23.061975+00:00
-- url     : https://prove2.me/theorems/b1e88246-afed-4e65-b350-e14caa48288a
-- title:
--   Homogeneous entropy is continuous on positive semidefinite matrices
-- statement:
--   Throughout, for a finite index type $n$ and $X\in M_n(\mathbb C)$, $H(X)$ denotes the frozen `finiteEntropy` of Frontier18.P01, the homogeneous entropy $H(X)=\max\bigl(0,\,-\operatorname{Tr}\eta(X)+\operatorname{Tr}X\,\log\operatorname{Tr}X\bigr)\in[0,\infty)$ with $\eta(x)=x\log x$ applied by the continuous functional calculus (natural logarithms, $0\log 0=0$). For a positive semidefinite $X\ne0$ this is $\operatorname{Tr}X\cdot S(X/\operatorname{Tr}X)$, with $S$ the von Neumann entropy, and $H(0)=0$. Let $(X_k)$ be a family of $n\times n$ complex matrices indexed along a filter $l$, eventually positive semidefinite, and converging entrywise to $Y$. Then
--
--   $$
--   H(X_k)	o H(Y)\quad	ext{along }l.
--   $$
--
--   Reason: on positive semidefinite matrices the eigenvalues depend continuously on the matrix, $\eta$ is continuous on $[0,\infty)$, and the trace is continuous; $Y$ is positive semidefinite as a limit of such matrices.
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

theorem finiteEntropy_tendsto {ι n : Type} [Fintype n] [DecidableEq n] {l : Filter ι}
    {X : ι → Matrix n n ℂ} {Y : Matrix n n ℂ} (hX : ∀ᶠ k in l, (X k).PosSemidef)
    (h : Tendsto X l (nhds Y)) :
    Tendsto (fun k => finiteEntropy (X k)) l (nhds (finiteEntropy Y)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P18

end
