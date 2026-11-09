-- Prove2me | Theorems.Thm_SemAC02_theorem_8_9_coin_formulas
-- name    : SemAC02.theorem_8_9_coin_formulas
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:29:30.430557+00:00
-- url     : https://prove2.me/theorems/b2f1aa96-938d-48df-8ed5-83892347d852
-- title:
--   Theorem 8.9 (Limaye et al.) — small-depth monotone formulas for the $\epsilon$-coin problem
-- statement:
--   Fix $d\ge2$. For all sufficiently small $\epsilon>0$ there is a monotone AND/OR formula $T$ of depth at most $d$ and size $\exp\bigl(O_d(\epsilon^{-1/(d-1)})\bigr)$ that solves the $\epsilon$-coin problem with error at most $1/10$:
--   $$
--   \Pr_{x\sim\mathrm{Bern}((1-\epsilon)/2)^m}[T(x)=1]\le\tfrac1{10},\qquad \Pr_{x\sim\mathrm{Bern}((1+\epsilon)/2)^m}[T(x)=0]\le\tfrac1{10}.
--   $$
--
--   The paper cites this result of Limaye et al. [52]; it is the starting point of the approximate-majority gadget of §8.3.
--
--   Differences from the source:
--   - encoding: O_d(ε^{−1/(d−1)}), "for all sufficiently small ε > 0" → one constant A (and ε₀ > 0) chosen before ε; ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀); reason: standard reading of O_d(·) and "for all sufficiently small ε"; the constants depend on d only
--   - encoding: formula (circuit with the paper's conventions of p.17) and its size → Circ tree in normal form (IsReduced), size = treeSize (number of nodes); reason: the paper's circuits are flattened with no repeated children by definition; for a formula the size is its number of nodes
--   - encoding: Pr over Bern(p)^m → bernProb p, the explicit finite sum; reason: same numbers
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Theorem 8.9, p.66 (PDF p.68)

import Mathlib
import Definitions.Def_SemAC02_Circ
import Definitions.Def_SemAC02_bernProb
import Definitions.Def_SemAC02_IsCoinDistinguisher

namespace SemAC02

/-- **Theorem 8.9 (Limaye et al. [52])** (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof
Systems*, manuscript (STOC 2027 submission), Theorem 8.9, p.66): fix `d ≥ 2`.
For all sufficiently small `ϵ > 0`, there is a monotone AND/OR formula of depth at most `d` and
size `exp(O_d(ϵ^{−1/(d−1)}))` solving the `ϵ`-coin problem with error at most `1/10`.

The paper cites this result; its proof is in Limaye et al. [52].

**Formalization Note** `O_d(·)` is one constant `A` (depending on `d` only) chosen before
`ϵ`; "sufficiently small" is `∃ ϵ₀ > 0, ∀ ϵ ∈ (0, ϵ₀)`. The formula is a `Circ (Fin m)` on some
number `m` of inputs, in the paper's normal form (`IsReduced`); its size is the tree size. -/
theorem theorem_8_9_coin_formulas (d : ℕ) (hd : 2 ≤ d) :
    ∃ A ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ (m : ℕ) (T : Circ (Fin m)), IsMonotoneCirc T ∧ IsReduced T ∧ T.depth ≤ d ∧
        (T.treeSize : ℝ) ≤ Real.exp (A * ε ^ (-1 / ((d : ℝ) - 1))) ∧
        IsCoinDistinguisher ε (1 / 10) (fun x => T.eval x) := by sorry

end SemAC02
