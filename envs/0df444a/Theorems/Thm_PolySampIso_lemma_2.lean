-- Prove2me | Theorems.Thm_PolySampIso_lemma_2
-- name    : PolySampIso.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:28:07.60829+00:00
-- url     : https://prove2.me/theorems/cadc760d-7ff3-400a-bb0e-85fdb978c00e
-- title:
--   Lemma 2, p.11 — the log barrier is the log-Laplace transform of a convolution of exponential rays
-- statement:
--   Let $X=\{x\in\mathbb R^n:Ax<b\}$ be a nonempty bounded polytope with rows $a_1,\dots,a_m$ of $A$, and $\psi(x)=-\sum_i\log(b_i-\langle a_i,x\rangle)$ its log barrier. For each $i$ let $\rho_i$ be the measure on the ray $\{ta_i:t>0\}$ obtained by pushing $e^{-tb_i}\mathbb 1_{t>0}\,dt$ forward under $t\mapsto ta_i$, and let $\rho=\rho_1*\cdots*\rho_m$. Then for every $x\in X$
--
--   $$\int_{\mathbb R^n}e^{\langle x,y\rangle}\,\rho(dy)=e^{\psi(x)},$$
--
--   that is, $\psi=\varphi^\sharp$ where $e^{-\varphi}$ is the density of $\rho$.
--
--   This identifies the log barrier as a log-Laplace transform, which is what lets the functional stochastic localization sampler of [GST26] run with $\psi$ as its geometry; the dual measure $\rho$ is also what makes the forwards step exact (Proposition 2).
--
--   Differences from the source:
--   - encoding: exp(−φᵢ), a density on span(aᵢ) supported on Rᵢ → the measure on ℝⁿ it defines (pushforward of exp(−t bᵢ)𝕀_{t>0}dt by t ↦ t aᵢ); the convolution exp(−φ₁) ∗ ⋯ ∗ exp(−φ_m) is the convolution of these measures; reason: Definition 1 interprets exp(−φ) on a subspace as a density against Lebesgue measure there; the measure carries the same information
--   - encoding: ψ = φ♯ for ψ defined in (7) → ∫ e^{⟨x,y⟩} ρ(dy) = e^{ψ(x)} for every x ∈ X; reason: ψ is defined on X in (7); φ♯(x) = log of the integral
--   - encoding: the standing assumption of §2.3 (a nonempty, full-dimensional, bounded polytope; A full-rank) → X = {Ax < b} nonempty and bounded, n ≥ 1; reason: X is open, so nonempty means full-dimensional; nonempty and bounded imply full column rank
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 2, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_PolySampIso_LogBarrier
import Definitions.Def_PolySampIso_LLT
import Definitions.Def_PolySampIso_Forwards

open MeasureTheory

namespace PolySampIso

/-- **Lemma 2** (the log barrier is a log-Laplace transform).

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 2, p.11 (PDF p.13):

"Lemma 2. For each i ∈ [m], define Ri := {y ∈ Rn | y = tai, t > 0}. Let exp(−φi) be the density on
span(ai), supported on Ri, induced by the pushforward of exp(−tbi)It>0dt by t ↦ tai. Define
exp(−φ) := exp(−φ1) ∗ · · · ∗ exp(−φm). Then ψ = φ♯ for ψ defined in (7)."

**Formalization Note.** `dualMeasure A b` is the measure of `exp(−φ)`: the convolution of the
pushforwards `facetMeasure A b i` of `exp(−t bᵢ)𝕀_{t>0}dt` under `t ↦ t aᵢ`. `ψ = φ♯` is
`IsLLTOn`: `∫ e^{⟨x,y⟩} ρ(dy) = e^{ψ(x)}` for every `x ∈ X`, the domain of `ψ` in (7). The standing
assumption of §2.3 (`X` nonempty and bounded, `n ≥ 1`) is kept. -/
theorem lemma_2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hX : StandingAssumption A b) (hn : 0 < n) :
    IsLLTOn (dualMeasure A b) (logBarrier A b) (polytope A b) := by sorry

end PolySampIso
