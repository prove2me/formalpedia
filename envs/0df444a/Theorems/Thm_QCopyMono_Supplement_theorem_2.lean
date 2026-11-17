-- Prove2me | Theorems.Thm_QCopyMono_Supplement_theorem_2
-- name    : QCopyMono.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:21:09.846609+00:00
-- url     : https://prove2.me/theorems/a9dff73d-8f8b-4aad-9b69-ca4bc943af3f
-- title:
--   Theorem 2 — testing monotonicity needs $\Omega(\min\{n/\varepsilon^3,\,n^{3/2}/\varepsilon^2\})$ copies of $|\psi_f\rangle$ for $2^{-\sqrt n/200}\le\varepsilon\le1/128$
-- statement:
--   Let $|\psi_f\rangle=2^{-n/2}\sum_{x\in\{0,1\}^n}|x,f(x)\rangle$ be the quantum function state of $f:\{0,1\}^n\to\{0,1\}$. There is an absolute constant $c>0$ such that for every $n$ and every $\varepsilon$ with
--
--   $$
--   2^{-\sqrt n/200}\le\varepsilon\le\frac1{128},
--   $$
--
--   every quantum algorithm that receives $t$ copies of $|\psi_f\rangle$ and decides, with success probability at least $2/3$, whether $f$ is monotone or $\varepsilon$-far from monotone uses
--
--   $$
--   t\ \ge\ c\cdot\min\Big\{\frac{n}{\varepsilon^{3}},\ \frac{n^{3/2}}{\varepsilon^{2}}\Big\}
--   $$
--
--   copies. Here a quantum algorithm on $t$ copies is an arbitrary two-outcome joint measurement on $|\psi_f\rangle^{\otimes t}$, and success probability $2/3$ means it accepts every monotone $f$ with probability at least $2/3$ and every $\varepsilon$-far $f$ with probability at most $1/3$.
--
--   Together with Theorem 1 this determines the copy complexity of monotonicity testing in the quantum sample model up to a constant factor in this range of $\varepsilon$.
--
--   **Formalization Note** The algorithm is the base mission's `IsMonoTester ε (1/3) t E`: an accepting effect $E$ on the $t$-copy register, fixed before $f$. The constant $c$ is chosen before $n$, $\varepsilon$, $t$ and $E$. $n^{3/2}$ is the real power.
--
--   Differences from the source:
--   - reading: Ω(min{n/ε^3, n^{3/2}/ε^2}) for 2^{−√n/200} ≤ ε ≤ 1/128 → one absolute c > 0 with c·min{n/ε³, n^{3/2}/ε²} ≤ t for every n and every ε in the range; reason: the range is empty unless √n ≥ 1400, and for each fixed n a tester needs t ≥ 1 (an ε-far function exists and a 0-copy effect accepts with a constant probability) while the bound is finite, so the all-n form is equivalent to the asymptotic Ω
--   - encoding: "any quantum algorithm … with success probability at least 2/3" → every effect E with IsMonoTester ε (1/3) t E (accept monotone f with probability ≥ 2/3, ε-far f with probability ≤ 1/3); reason: every t-copy measurement followed by a yes/no decision induces such an effect; the proof states "two-sided error at most 1/3" (p.29)
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), Theorem 2, p.4; proof §4, pp.17–29, eq. (50)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QCopyMono_IsMonoTester

namespace QCopyMono

namespace Supplement

open QAlgorithms

/-- Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), Theorem 2 (Lower bound), p.4 (proved in §4,
pp.17–29, conclusion (50)): for `2^{−√n/200} ≤ ε ≤ 1/128`, any quantum algorithm requires
`Ω(min{n/ε³, n^{3/2}/ε²})` copies of `|ψ_f⟩` to decide, with success probability at least `2/3`,
whether `f` is monotone or `ε`-far from monotone.

**Formalization Note.** The `Ω(·)` is one absolute constant `c > 0`, chosen before `n`, `ε`,
`t` and the algorithm. An algorithm on `t` copies is any two-outcome joint measurement, given by
its accepting effect `E` (the published `IsMonoTester` model; this covers adaptive and entangled
strategies). "Success probability at least `2/3`" is two-sided error `1/3`
(`IsMonoTester ε (1/3) t E`; the proof's "two-sided error at most 1/3", p.29). The statement is
for every `n`: the range of `ε` is empty unless `√n ≥ 1400`, and for each fixed `n` a tester
needs `t ≥ 1` while the bound is finite, so this is the asymptotic `Ω` with no threshold.
`n^{3/2}` is the real power and `√n` is `Real.sqrt n`. -/
theorem theorem_2 :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∀ ε : ℝ, (2 : ℝ) ^ (-Real.sqrt n / 200) ≤ ε → ε ≤ 1 / 128 →
      ∀ (t : ℕ) (E : Matrix (Fin t → X n) (Fin t → X n) ℂ), IsMonoTester ε (1 / 3) t E →
        c * min ((n : ℝ) / ε ^ 3) ((n : ℝ) ^ (3 / 2 : ℝ) / ε ^ 2) ≤ (t : ℝ) := by sorry

end Supplement

end QCopyMono
