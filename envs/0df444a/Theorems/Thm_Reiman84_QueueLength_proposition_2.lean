-- Prove2me | Theorems.Thm_Reiman84_QueueLength_proposition_2
-- name    : Reiman84.QueueLength.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T12:48:59.79682+00:00
-- url     : https://prove2.me/theorems/7d6faae2-bb12-463b-abae-fac353987a5c
-- title:
--   Proposition 2 — f(x) = φ(x) for x ∈ C₊
-- statement:
--   Let $P$ be a nonnegative matrix with spectral radius strictly less than one. For $x\in D^K$ let $f(x)(t)=x(t)+y(t)[I-P]$, where $y$ is the least element of $U(x)$ (Proposition 1). For $x\in C_+$, with $\phi$ the reflection mapping of Lemma 1,
--   $$f(x)=\phi(x)\quad\text{on } [0,1].$$
--
--   Combined with $Q=f(\tilde X)$ this identifies the queue length process with the reflection of $\tilde X$ whenever the latter is continuous, and in the limit.
--
--   **Formalization Note** $f(x)$ lives in $D$ (time $[0,1]$) and $\phi(x)$ in $C$ (time $[0,\infty)$); they are compared on $[0,1]$. Spectral radius $<1$ is $P^m\to0$.
-- source:
--   Reiman, Open Queueing Networks in Heavy Traffic, Math. Oper. Res. 9(3) (1984), p. 445, Proposition 2

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths

namespace Reiman84.QueueLength

open Filter Topology

/-- Proposition 2, p. 445: for `x ∈ C_+`, `f(x) = φ(x)`, where `f(x)(t) = x(t) + y(t)[I − P]`
with `y` the least element of `U(x)`, compared on `[0, 1]` (the domain of `D`). -/
theorem proposition_2 {K : ℕ} (P : Matrix (Fin K) (Fin K) ℝ) (hP0 : ∀ i j, 0 ≤ P i j)
    (hP : Tendsto (fun m : ℕ => P ^ m) atTop (𝓝 0))
    (x y z yU : ℝ → Fin K → ℝ) (hxyz : IsReflectionPair P x y z) (hU : IsLeastU P x yU) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, x t + Matrix.vecMul (yU t) (1 - P) = z t := by sorry

end Reiman84.QueueLength
