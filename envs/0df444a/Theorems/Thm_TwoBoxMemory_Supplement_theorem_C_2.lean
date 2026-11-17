-- Prove2me | Theorems.Thm_TwoBoxMemory_Supplement_theorem_C_2
-- name    : TwoBoxMemory.Supplement.theorem_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:14:24.461006+00:00
-- url     : https://prove2.me/theorems/7b3ff7c4-c4c7-410c-9d9e-2ab1e2d15b29
-- title:
--   Theorem C.2 — rational controllers are dense in risk at the same label budget
-- statement:
--   Fix failure probabilities $r,s\in(0,1)$ and costs $C,D>0$. A controller with $m$ labels is a probability row $\mu$ and nonnegative $m\times m$ matrices $K_A,K_B$ with $(K_A+K_B)\mathbf 1=\mathbf 1$; with $Q_A=rK_A+K_B$, $Q_B=K_A+sK_B$, $c=CK_A\mathbf 1+DK_B\mathbf 1$ its two conditional risks are $J_h=\sum_{n\ge0}\mu Q_h^nc\in[0,\infty]$ and its worst risk is $W=\max(J_A,J_B)$. $V_M$ is the infimum of $W$ over all real controllers with at most $M$ labels.
--
--   1. For every real controller with at most $M$ labels and finite worst risk, and every $\delta>0$, there is a rational controller with at most $M$ labels whose two conditional risks are finite and satisfy $|J'_h-J_h|<\delta$ for $h=A$ and $h=B$.
--   2. Consequently, for rational $r,s,C,D$ and every $M$,
--
--   $$V_M=\inf\{W(K_A,K_B,\mu):\ K_A,K_B,\mu\ \text{rational, at most }M\text{ labels}\}.$$
--
--   The theorem connects the real controller class of the lower bounds with the rational controllers that finite certificates can check.
--
--   Differences from the source:
--   - encoding: the two risks of the approximant differ from the original ones by less than δ → each approximant risk is finite and the `toReal` distance of the two risks is below δ, for h = A and h = B; reason: a finite difference requires finite risks; the original risks are finite by hypothesis
--   - encoding: rational physical inputs → `r s C D : ℚ` cast to ℝ, with 0 < r, s < 1 and C, D > 0; reason: Lean convention; same instances
--   - encoding: commands A, B; risks in [0, ∞] → commands `Fin 2` with 0 = A, 1 = B; risks in `ℝ≥0∞`; reason: Lean convention; same instances
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), Theorem C.2, p.29 (PDF 31); Appendix C standing assumptions, p.28 (PDF 30)

import Mathlib
import Definitions.Def_TwoBoxMemory_Controller
import Definitions.Def_TwoBoxMemory_Supplement_Rational

namespace TwoBoxMemory.Supplement

open TwoBoxMemory

/-- Theorem C.2 (Rational controllers are dense in risk at the same budget). Fix `0 < r, s < 1`
and `C, D > 0`.
1. For every finite-risk real controller with at most `M` labels and every `δ > 0`, there is a
   rational controller with at most `M` labels whose two conditional risks are finite and differ
   from the original risks by less than `δ`.
2. Consequently, for rational physical inputs (`r, s, C, D ∈ ℚ`),
   `V_M = inf{W(K_A, K_B, µ) : K_A, K_B, µ rational, at most M labels}`.

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
Theorem C.2, p.29 (PDF 31); standing assumptions of Appendix C, p.28 (PDF 30).

**Formalization Note.** Controllers, the two risks `∑_n µ Q_h^n c` (`ctrlRisk`, in `ℝ≥0∞`), `W`
(`worstRisk`) and `V_M` (`memValue`, real entries, `m ≤ M` labels) are the published base
definitions. "Finite-risk" is `worstRisk < ⊤`; the risk difference is taken between `toReal`s of
finite risks. The paper's remark that the rational infimum need not be attained is not a claim and
is not stated. -/
theorem theorem_C_2 :
    (∀ (r s C D : ℝ), 0 < r → r < 1 → 0 < s → s < 1 → 0 < C → 0 < D →
      ∀ (M m : ℕ), m ≤ M → ∀ κ : Controller m, worstRisk r s C D κ < ⊤ →
        ∀ δ : ℝ, 0 < δ →
          ∃ (m' : ℕ) (κ' : Controller m'), m' ≤ M ∧ IsRationalCtrl κ' ∧
            ∀ h : Fin 2, ctrlRisk r s C D κ' h < ⊤ ∧
              |(ctrlRisk r s C D κ' h).toReal - (ctrlRisk r s C D κ h).toReal| < δ) ∧
    (∀ (r s C D : ℚ), 0 < r → r < 1 → 0 < s → s < 1 → 0 < C → 0 < D → ∀ M : ℕ,
      memValue r s C D M =
        ⨅ (m : ℕ) (_ : m ≤ M) (κ : Controller m) (_ : IsRationalCtrl κ),
          worstRisk r s C D κ) := by sorry

end TwoBoxMemory.Supplement
