-- Prove2me | Theorems.Thm_RQCMoments_Supplement_theorem_5_8
-- name    : RQCMoments.Supplement.theorem_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:51:30.709054+00:00
-- url     : https://prove2.me/theorems/85ef220a-f942-4adf-a813-9645d0437507
-- title:
--   Theorem 5.8 — some $\varepsilon$-approximate $k$-design is $\Omega(\sqrt{D/(k(D+k))}+\varepsilon)$ from Porter–Thomas in Kolmogorov distance
-- statement:
--   For integers $D\ge2$, $k\ge1$ and $\varepsilon\in[0,1]$, there is an $\varepsilon$-approximate unitary $k$-design $\mu$ on $U(D)$ such that the squared magnitude of its top-left entry is at Kolmogorov distance
--
--   $$\sup_{z\in\mathbb R}\Big|\Pr_{U\sim\mu}\big[|U_{00}|^2\le z\big]-F_{\mathrm{Beta}(1,D-1)}(z)\Big|=\Omega\Big(\sqrt{\tfrac{D}{k(D+k)}}+\varepsilon\Big)$$
--
--   from $\mathrm{Beta}(1,D-1)$, with an absolute constant in the $\Omega$.
--
--   This shows that the upper bound of Theorem 4.9, the goal of the base mission, is tight up to a constant factor.
--
--   **Formalization Note** The $\Omega$ is one absolute constant $c>0$ chosen before $D,k,\varepsilon$. The design is `IsStrongDesign μ k k ε` (Remark 2.3), the top-left entry is `entry 0 0` and $\mathrm{Beta}(1,D-1)$ is `porterThomas D`. The Kolmogorov distance is a real supremum over $z$; every term lies in $[0,1]$.
--
--   Differences from the source:
--
--   - encoding: Kolmogorov distance Ω(√(D/(k(D+k))) + ε) → ∃ c > 0 (before D, k, ε) with c·(√(D/(k(D+k))) + ε) ≤ sup_z |μ(|U₀₀|² ≤ z) − F_{Beta(1,D−1)}(z)|; reason: asymptotic notation with absolute constants chosen first; same content
--   - encoding: ε-approximate unitary k-design (Remark 2.3) → IsStrongDesign μ k k ε (published; probability measure, literal completely positive order); reason: Remark 2.3 fixes this meaning; same instances
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 5.8, p.37 (PDF p.39)

import Mathlib
import Definitions.Def_RQCMoments_IsStrongDesign
import Definitions.Def_RQCMoments_entry
import Definitions.Def_RQCMoments_porterThomas

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

namespace Supplement

/-- **Theorem 5.8** (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 5.8, p.37, PDF p.39).
For integers `D ≥ 2` and `k ≥ 1` and `ε ∈ [0,1]`, there exists an `ε`-approximate unitary `k`-design
on `U(D)` such that the squared magnitude of its top-left entry is at Kolmogorov distance
`Ω(√(D/(k(D+k))) + ε)` from `Beta(1, D − 1)`.

**Formalization Note** The `Ω(·)` is one absolute constant `c > 0` chosen before `D`, `k`, `ε`. An
`ε`-approximate unitary `k`-design is `IsStrongDesign μ k k ε` (Remark 2.3). The Kolmogorov distance
(2) is the real supremum over `z` of `|μ(|U₀₀|² ≤ z) − F_{Beta(1,D−1)}(z)|`; for a design (a
probability measure) and `D ≥ 2` every term lies in `[0,1]`, so the supremum is a genuine one.
The top-left entry is `entry 0 0`; `Beta(1, D−1)` is the published `porterThomas D`. -/
theorem theorem_5_8 :
    ∃ c : ℝ, 0 < c ∧ ∀ D : ℕ, (hD : 2 ≤ D) → ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∃ μ : Measure (Matrix.unitaryGroup (Fin D) ℂ), IsStrongDesign μ k k ε ∧
        c * (Real.sqrt ((D : ℝ) / ((k : ℝ) * ((D : ℝ) + k))) + ε) ≤
          ⨆ z : ℝ, |(μ {U | entry (⟨0, by omega⟩ : Fin D) ⟨0, by omega⟩ U ≤ z}).toReal -
            (porterThomas D (Set.Iic z)).toReal| := by sorry

end Supplement

end RQCMoments
