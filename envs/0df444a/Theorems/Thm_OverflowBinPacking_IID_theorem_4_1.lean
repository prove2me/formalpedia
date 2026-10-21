-- Prove2me | Theorems.Thm_OverflowBinPacking_IID_theorem_4_1
-- name    : OverflowBinPacking.IID.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:45.410266+00:00
-- url     : https://prove2.me/theorems/ad6e6988-0382-4ebb-aab3-bc477c1721a5
-- title:
--   Theorem 4.1, pp. 10–11 (= Theorem 1.1) — conversion to a risk-budgeted policy
-- statement:
--   Let $X_1,\ldots,X_n$ be independent nonnegative item sizes, $C\ge1$, and $\gamma>0$. Every deterministic feasible policy $P$ has a policy $P'$ for the same items that isolates each item with $\Pr(X_i>1)>\gamma/C$ in its own bin and keeps every other bin's accumulated risk at most $\gamma/C$. Its expected cost obeys
--   $$\operatorname{cost}(P')\le\left(1+\frac{2}{\gamma}\right)\operatorname{cost}(P).$$
--   When all items satisfy $\Pr(X_i>1)\le\gamma/C$, the converted policy is fully risk-budgeted. This provides the structural bridge from an arbitrary comparator to the policies analyzed for i.i.d. inputs.
--
--   **Formalization Note** Policies are measurable. The heavy-item clause is the footnote to Theorem 1.1 on p. 4 and the first bullet of Theorem 4.1 on p. 11.
-- source:
--   Perez-Salazar, Singh & Toriello, Adaptive Bin Packing with Overflow, arXiv:2007.11532v2, p. 4, Theorem 1.1 and footnote 2; pp. 10–11, Theorem 4.1

import Mathlib
import Definitions.Def_OverflowBinPacking_IID_Model

namespace OverflowBinPacking.IID

open MeasureTheory

/-- Theorem 4.1, pp. 10–11 (= Theorem 1.1, p. 4): every policy
has a heavy-isolating, risk-budgeted counterpart at factor `1 + 2 / γ`. -/
theorem theorem_4_1 {n : ℕ} (μ : Fin n → Measure ℝ)
    (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hμ0 : ∀ i, μ i (Set.Iio 0) = 0)
    (C γ : ℝ) (hC : 1 ≤ C) (hγ : 0 < γ)
    (a : Rule n) (ha : IsPolicy a) :
    ∃ a' : Rule n, IsPolicy a' ∧ IsolatesHeavy μ C γ a' ∧
      cost μ C a' ≤ (1 + 2 / γ) * cost μ C a := by sorry

end OverflowBinPacking.IID
