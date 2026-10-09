-- Prove2me | Theorems.Thm_TeschlODE_IntervalMaps_tentRepellor_dimH
-- name    : TeschlODE.IntervalMaps.tentRepellor_dimH
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T19:05:33.753447+00:00
-- url     : https://prove2.me/theorems/5e20b439-2caf-40c5-bb90-b54c7857b5e3
-- title:
--   Theorem 11.20 — dim_H of the tent-map repellor is log 2 / log µ; for µ > 2 it is a strange repellor
-- statement:
--   Let $\mu \ge 2$ and let $\Lambda = \{x \in \mathbb{R} : T_\mu^n(x) \in [0,1]\ \forall n \ge 0\}$ be the repellor of the tent map $T_\mu(x) = \frac{\mu}{2}(1 - |2x-1|)$. Then
--   $$\dim_H(\Lambda) = \frac{\log 2}{\log \mu}, \qquad \mu \ge 2, \tag{11.49}$$
--   and, for $\mu > 2$, $\Lambda$ is a strange repellor of $T_\mu$: it is compact with $T_\mu(\Lambda) = \Lambda$, it has a neighborhood that every orbit starting there outside $\Lambda$ eventually leaves, $(\Lambda, T_\mu|_\Lambda)$ is topologically transitive and chaotic, and $\dim_H(\Lambda)$ is not an integer.
--
--   This is the chapter's capstone: it combines the symbolic description of $\Lambda$ (Theorem 11.5 and Lemmas 11.8–11.9) with a computation of Hausdorff dimension.
--
--   **Formalization Note.** The book asserts "in particular, it is a strange repellor" for all $\mu \ge 2$. For $\mu = 2$ the set $\Lambda$ is $[0,1]$ (proof, p. 310), of dimension $1$, an integer, so it is not fractal and the clause is false there; the statement therefore gives the dimension formula for $\mu \ge 2$ and the strange-repellor clause for $\mu > 2$ only. $\dim_H$ is Mathlib's `dimH`, valued in $[0,\infty]$; the right-hand side is the positive real $\log 2/\log \mu$ embedded by `ENNReal.ofReal`.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 309, Theorem 11.20

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TeschlODE_Shared_tentRepellor
import Definitions.Def_TeschlODE_IntervalMaps_IsStrangeRepellor

namespace TeschlODE.IntervalMaps

/-- Teschl, Theorem 11.20, p. 309: the Hausdorff dimension of the repellor `Λ` of the tent map
`T_µ` is `dim_H(Λ) = log(2)/log(µ)` for `µ ≥ 2` (11.49), and, for `µ > 2`, `Λ` is a strange
repellor of `T_µ` (repelling, topologically transitive, `(Λ, T_µ)` chaotic, `Λ` fractal).
Correction to the page: the book claims "strange repellor" for all `µ ≥ 2`, but for `µ = 2`,
`Λ = [0, 1]` has dimension `1`, an integer, so the clause is stated for `µ > 2` only. -/
theorem tentRepellor_dimH (μ : ℝ) (hμ : 2 ≤ μ) :
    dimH (TeschlODE.Shared.tentRepellor μ) = ENNReal.ofReal (Real.log 2 / Real.log μ) ∧
      (2 < μ → IsStrangeRepellor (TeschlODE.Shared.tentMap μ) (TeschlODE.Shared.tentRepellor μ)) := by sorry

end TeschlODE.IntervalMaps
