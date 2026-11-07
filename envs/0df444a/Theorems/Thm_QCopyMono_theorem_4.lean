-- Prove2me | Theorems.Thm_QCopyMono_theorem_4
-- name    : QCopyMono.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:43:25.310206+00:00
-- url     : https://prove2.me/theorems/a6e09e68-becc-4a6f-85ee-ad9d9af7c5ed
-- title:
--   Theorem 4 — directed isoperimetric inequality $\mathbb E_x\big[\sqrt{I^-_{f,\mathrm{col}}(x)}\big]\ge\kappa\varepsilon$ [PRW22]
-- statement:
--   There is an absolute constant $\kappa>0$ such that for every Boolean function $f:\{0,1\}^n\to\{0,1\}$ that is $\varepsilon$-far from monotone and every coloring $\mathrm{col}$ of the violated edges $E^-_f$ into red and blue,
--   $$
--   \mathbb E_{x\sim\mathrm{Unif}(\{0,1\}^n)}\Big[\sqrt{I^-_{f,\mathrm{col}}(x)}\Big]\ge\kappa\varepsilon .
--   $$
--   The paper cites this as [PRW22, Theorem 2.9] and does not prove it. It is the structural input that removes a logarithmic factor from the path tester's copy count.
--
--   Differences from the source:
--   - generalization: ε-far with ε the distance parameter (ε > 0) → every real ε; reason: for ε ≤ 0 the bound is immediate since the left side is non-negative; the statement specializes to the printed one
--   - encoding: a coloring col : E^-_f → {red, blue} → a function on ordered pairs (lower, upper), read only on violated edges; reason: every coloring of E^-_f extends to such a function; same instances
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), Theorem 4, p.11, eq. (11)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QCopyMono_IsMonoTester
import Definitions.Def_QCopyMono_ViolatedEdge

namespace QCopyMono

open QAlgorithms

/-- Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), Theorem 4, p.11 ([PRW22, Theorem 2.9], cited and
not proved in the paper): there is an absolute constant `κ > 0` such that for every
`f : {0,1}ⁿ → {0,1}` that is `ε`-far from monotone and every red/blue coloring `col` of `E⁻_f`,
`E_x[√(I⁻_{f,col}(x))] ≥ κ ε` (eq. (11)).

**Formalization Note.** A coloring is a function on ordered pairs (lower, upper), read only on
violated edges (`true` = red). `κ` is chosen before `n`, `f`, `ε`, `col`. -/
theorem theorem_4 :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (n : ℕ) (f : Qubits n → Bool) (ε : ℝ)
      (col : Qubits n → Qubits n → Bool), IsFar ε f →
        κ * ε ≤ (∑ x : Qubits n, Real.sqrt (inflMinus f col x)) / 2 ^ n := by sorry

end QCopyMono
