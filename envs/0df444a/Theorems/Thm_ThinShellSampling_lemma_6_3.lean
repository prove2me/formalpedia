-- Prove2me | Theorems.Thm_ThinShellSampling_lemma_6_3
-- name    : ThinShellSampling.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:48:03.12638+00:00
-- url     : https://prove2.me/theorems/f177dc71-d48d-4785-8a63-15f2e8089ba4
-- title:
--   Lemma 6.3 — Phase-I closeness of the lifted annealing laws
-- statement:
--   Let $V:\mathbb R^n\to\mathbb R\cup\{\infty\}$ be convex with $B(0,1)\subseteq L_g$ and $\int e^{-V}<\infty$, $n\ge1$, and let $\mu_{\sigma^2,\rho}$ be the annealing laws (6.1) on the truncated epigraph $\bar K$. Put $\nu_s=\mu_{n^{-1},s}$ for $s>0$. There is a universal constant $C$ such that for $q>1$ and $0\le\alpha<(q-1)^{-1}$ with $(1+\alpha)s\le n$,
--
--   $$
--   \mathsf R_q(\nu_s\,\|\,\nu_{(1+\alpha)s})\le C\,\frac{qn\alpha^2}{[1-(q-1)\alpha]^2}.
--   $$
--
--   It justifies the Phase-I update $\rho\leftarrow\rho\big(1+c/\sqrt{q_0(q_0+n)}\big)$ (6.2) of Algorithm 6.6.
--
--   Differences from the source:
--
--   - encoding: ≲ → a universal constant C > 0, chosen before n and V; reason: the paper's convention (§1.3, p.12)
--   - encoding: standing assumptions of §6 and the truncation radius D = 1 ∨ Rℓ → IsStandardPotential V and R = (E_π‖X‖²)^{1/2} in K̄; reason: the section's standing objects, made explicit
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), Lemma 6.3, p.37 (PDF p.39); setting §6.2–6.3, pp.35–36

import Mathlib
import Definitions.Def_ThinShellSampling_renyi
import Definitions.Def_ThinShellSampling_muAnneal

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory
open scoped ENNReal

/-- **Lemma 6.3 (Phase-I closeness of the lifted annealing laws).**

Y. Kook, S. S. Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave
Sampling with Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256
25a041a9…), Lemma 6.3, p.37 (PDF p.39), with `µ_{σ²,ρ}` from (6.1) and `K̄` from §6.2 under the standing
assumptions of §6 (`V` convex, `B(0, 1) ⊆ L_g`): "Let `ν_s := µ_{n⁻¹,s}` for `s > 0`. Then, for `q > 1` and
`0 ≤ α < (q − 1)⁻¹` such that `(1 + α) s ≤ n`, `R_q(ν_s ‖ ν_{(1+α)s}) ≲ qnα² / [1 − (q − 1) α]²`."

**Formalization Note.** `≲` is a universal constant `C`, chosen before `n` and `V`. The truncation
uses `R = (E_π‖X‖²)^{1/2}` (`Rrad V`), as in §6.2. -/
theorem lemma_6_3 :
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ V : EuclideanSpace ℝ (Fin n) → WithTop ℝ, IsStandardPotential V →
      ∀ s q α : ℝ, 0 < s → 1 < q → 0 ≤ α → α < (q - 1)⁻¹ → (1 + α) * s ≤ n →
      renyi q (muAnneal V (Rrad V) (1 / n) s) (muAnneal V (Rrad V) (1 / n) ((1 + α) * s)) ≤
        ENNReal.ofReal (C * (q * n * α ^ 2 / (1 - (q - 1) * α) ^ 2)) := by sorry

end ThinShellSampling
