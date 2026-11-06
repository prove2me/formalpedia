-- Prove2me | Theorems.Thm_PolarizedLearning_limit_bias
-- name    : PolarizedLearning.limit_bias
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:18:47.806435+00:00
-- url     : https://prove2.me/theorems/fe334367-7df0-48a1-8dc1-8b86d38230f1
-- title:
--   (EC.6), p. ec2 — under Assumption 1, $L+(H-L)\int f(\pi,H)\,d\nu<H$ when $\pi^-(x)<1$, and the mirror bound for $q=L$
-- statement:
--   Fix the model parameters, a statistic $x\in[0,1]$, and a probability measure $\nu$ on $\mathbb R$ carried by the ML beliefs, $\nu(\Pi(x))=1$, such that $\nu\bigl((\pi^-(x),\pi^+(x))\bigr)>0$ whenever $\pi^-(x)<\pi^+(x)$ (Assumption 1). Then:
--
--   1. if $\pi^-(x)<1$, $$L+(H-L)\int f(\pi,H)\,d\nu(\pi)<H;$$
--   2. if $\pi^+(x)>0$, $$L+(H-L)\int f(\pi,L)\,d\nu(\pi)>L.$$
--
--   Applied at the limit point of the consumption rate with $\nu=\Psi(x_\infty)$, this is the strict bias of the long-run expected quality estimate.
--
--   Differences from the source:
--   - generalization: Ψ∞ ∈ ∆([π−(x*(H)), π+(x*(H))]) at the stable point x*(H) → any probability measure ν with ν(Π(x)) = 1 at any x ∈ [0,1] with π⁻(x) < 1; reason: specializes at x = x*(H), ν = Ψ(x*(H))
--   - reading: Assumption 1: no mass one on an end point of Π → ν((π⁻(x), π⁺(x))) > 0 only when π⁻(x) < π⁺(x); reason: on a singleton Π(x) the Dirac is the only distribution; literally the assumption cannot hold there (paper.md item 1)
--   - reading: 'The proof for q = L follows from symmetric argument and will be omitted' → 0 < π⁺(x) → L < L + (H − L)∫ f(π, L) dν; reason: the symmetric statement the q = L case needs
--   - reading: standing assumptions of pp. 8–11 (H > L, p > 0, L − p > 0, H + p < 1, u ∈ (0,1), [u−ϵ,u+ϵ] ⊆ [0,1], α > 0.5) → Params, which also requires ϵ > 0 and α < 1; reason: ϵ is called a degree of uncertainty and divided by on p. 17; the signal 'noisily reveals' quality (p. 11), and at α = 1 learning is complete (counterexample in paper.md item 3)
-- source:
--   Kadiyala–Shin, Social Learning and Content Quality under Polarization, MSOM (2024), doi:10.1287/msom.2022.0533, e-companion, proof of Theorem 2, (EC.6) and the sentences before it, p. ec2 (PDF 34)

import Mathlib
import Definitions.Def_PolarizedLearning_Model

open MeasureTheory

namespace PolarizedLearning

/-- **Strict bias of the expected quality under Assumption 1**, Kadiyala–Shin, *Social Learning and
Content Quality under Polarization*, MSOM (2024), doi:10.1287/msom.2022.0533, e-companion, proof
of Theorem 2, (EC.6), p. ec2 (PDF 34): `L + (H − L) E_{π̃∼Ψ∞}[f(π̃, H)] < H`.

Let `x ∈ [0,1]` and let `ν` be a probability measure on `ℝ` with `ν(Π(x)) = 1` that, when `Π(x)` is
not a singleton, gives positive mass to `(π⁻(x), π⁺(x))`. Then
1. if `π⁻(x) < 1`, then `L + (H − L) ∫ f(π, H) dν(π) < H`;
2. (the case `q = L`, omitted in the paper as symmetric) if `0 < π⁺(x)`, then
   `L < L + (H − L) ∫ f(π, L) dν(π)`. -/
theorem limit_bias (P : Params) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hsupp : ν (Pi P x) = 1)
    (hA1 : piMinus P x < piPlus P x → 0 < ν (Set.Ioo (piMinus P x) (piPlus P x))) :
    (piMinus P x < 1 → P.L + (P.H - P.L) * ∫ π, f P.al π .high ∂ν < P.H) ∧
    (0 < piPlus P x → P.L < P.L + (P.H - P.L) * ∫ π, f P.al π .low ∂ν) := by sorry

end PolarizedLearning
