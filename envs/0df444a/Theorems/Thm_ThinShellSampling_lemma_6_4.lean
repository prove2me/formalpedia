-- Prove2me | Theorems.Thm_ThinShellSampling_lemma_6_4
-- name    : ThinShellSampling.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:48:02.641508+00:00
-- url     : https://prove2.me/theorems/5f91c411-d37d-45a0-9531-372475fd8f5e
-- title:
--   Lemma 6.4 — closeness in the first loop of Phase II
-- statement:
--   Under the standing assumptions of §6 ($V$ convex, $B(0,1)\subseteq L_g$, $\int e^{-V}<\infty$, $n\ge1$), let $\mu_s=\mu_{s,n}$ for $s\in(0,1)$. There is a universal constant $C$ such that for $q>1$ and $\alpha>0$,
--
--   $$
--   \mathsf R_q(\mu_s\,\|\,\mu_{(1+\alpha)s})\le C\,qn\alpha^2.
--   $$
--
--   It justifies the update $\sigma^2\leftarrow(1+c/\sqrt{q_0n})\sigma^2$ of the first loop of Phase II, below $\sigma^2=1$.
--
--   Differences from the source:
--
--   - encoding: ≲ → a universal constant C > 0, chosen before n and V; reason: the paper's convention (§1.3, p.12)
--   - encoding: standing assumptions of §6 and the truncation radius D = 1 ∨ Rℓ → IsStandardPotential V and R = (E_π‖X‖²)^{1/2} in K̄; reason: the section's standing objects, made explicit
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), Lemma 6.4, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_ThinShellSampling_renyi
import Definitions.Def_ThinShellSampling_muAnneal

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory
open scoped ENNReal

/-- **Lemma 6.4 (closeness in the first loop of Phase II).**

Y. Kook, S. S. Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave
Sampling with Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256
25a041a9…), Lemma 6.4, p.38 (PDF p.40), with `µ_{σ²,ρ}` from (6.1) and `K̄` from §6.2 under the standing
assumptions of §6: "Let `µ_s := µ_{s,n}` for `s ∈ (0, 1)`. Then, for `q > 1` and `α > 0`,
`R_q(µ_s ‖ µ_{(1+α)s}) ≲ qnα²`."

**Formalization Note.** `≲` is a universal constant `C`, chosen before `n` and `V`. The truncation
uses `R = Rrad V`. -/
theorem lemma_6_4 :
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ V : EuclideanSpace ℝ (Fin n) → WithTop ℝ, IsStandardPotential V →
      ∀ s q α : ℝ, 0 < s → s < 1 → 1 < q → 0 < α →
      renyi q (muAnneal V (Rrad V) s n) (muAnneal V (Rrad V) ((1 + α) * s) n) ≤
        ENNReal.ofReal (C * (q * n * α ^ 2)) := by sorry

end ThinShellSampling
