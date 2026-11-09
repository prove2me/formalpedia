-- Prove2me | Theorems.Thm_PersistQMem_zeta_attained_budget_pos
-- name    : PersistQMem.zeta_attained_budget_pos
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:38:04.306878+00:00
-- url     : https://prove2.me/theorems/4e082ac6-7e12-408b-b6a8-163ec54b540b
-- title:
--   §2.1, pp.3–4 — $\zeta(q)$ is finite and attained; $\zeta(K)>0$, $\beta>0$, $B_K>0$
-- statement:
--   Fix the data of Definition 2.1: Hermitian $G_1,\dots,G_M$ with $\|G_j\|_{\mathrm{op}}\le1$ and $\operatorname{Tr}(\tau G_j)=0$, a prior $p_j>0$ with $\sum_jp_j=1$, and at least one $G_j\ne0$. Then:
--
--   1. $\operatorname{Tr}(TG_jTG_j)=\operatorname{Tr}[(T^{1/2}G_jT^{1/2})^2]\ge0$ for every $T\succeq0$;
--   2. for every integer $q\ge1$ the supremum
--   $$\zeta(q)=\sup_{T\succeq0,\ \operatorname{Tr}(T^2)=1,\ \operatorname{rank}T\le\min\{q,D\}}\ \sum_jp_j\operatorname{Tr}(TG_jTG_j)$$
--   is finite and attained by a feasible $T$;
--   3. for every integer $K\ge1$, $\zeta(K)>0$, $\beta>0$ and $B_K=\zeta(K)+(2K-2)\beta>0$.
--
--   This makes the bound of Theorem 2.2, which divides by $B_K$, meaningful.
--
--   Differences from the source:
--   - encoding: ζ(q) as a supremum, “finite” → sSup of the value set profileSet; finiteness as BddAbove; attainment as a feasible T whose value equals the sSup; reason: sSup is the supremum on a nonempty set that is bounded above, which the statement asserts
--   - encoding: Tr(TG_jTG_j) → its real part; reason: it is real for Hermitian T and G_j
--   - encoding: ‖·‖_op → opNorm, Mathlib's l2 operator norm on matrices; reason: Lean convention; same norm
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), §2.1, pp.3–4 (PDF pp.6–7)

import Mathlib
import Definitions.Def_PersistQMem_ProfileData

open scoped Matrix ComplexOrder

namespace PersistQMem

/-- **§2.1, pp.3–4 (unnumbered): the profile is finite and attained, and `β, ζ(K), B_K > 0`**
(Tao, Shen, *Structural Lower Bounds for Quantum Property Estimation with Persistent Memory*,
STOC 2027 submission, manuscript of 2026-11-03, sha256 6d48ad24…, §2.1, pp.3–4).
Under the data of Definition 2.1:
1. `Tr(T G_j T G_j) ≥ 0` for every `T ⪰ 0`;
2. for every `q ≥ 1` the supremum `ζ(q)` in (2) is finite (the value set is bounded above) and
   attained by a feasible `T`;
3. for every `K ≥ 1`, `ζ(K) > 0`, `β > 0` and `B_K > 0`.

**Formalization Note.** `Tr(T G_j T G_j)` is taken through its real part (it is real). -/
theorem zeta_attained_budget_pos {D M : ℕ} {G : Fin M → Matrix (Fin D) (Fin D) ℂ}
    {p : Fin M → ℝ} (hG : ProfileData G p) :
    (∀ T : Matrix (Fin D) (Fin D) ℂ, T.PosSemidef → ∀ j, 0 ≤ (T * G j * T * G j).trace.re) ∧
    (∀ q : ℕ, 1 ≤ q → BddAbove (profileSet G p q) ∧
      ∃ T : Matrix (Fin D) (Fin D) ℂ, T.PosSemidef ∧ (T * T).trace = 1 ∧ T.rank ≤ min q D ∧
        profile G p q = ∑ j, p j * (T * G j * T * G j).trace.re) ∧
    (∀ K : ℕ, 1 ≤ K → 0 < profile G p K ∧ 0 < gramNorm G p ∧ 0 < budget G p K) := by sorry

end PersistQMem
