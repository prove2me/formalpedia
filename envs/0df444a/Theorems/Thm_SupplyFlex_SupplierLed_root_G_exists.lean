-- Prove2me | Theorems.Thm_SupplyFlex_SupplierLed_root_G_exists
-- name    : SupplyFlex.SupplierLed.root_G_exists
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-20T05:37:56.910974+00:00
-- url     : https://prove2.me/theorems/2b5d4fdb-7e90-4681-8e48-f533050fca6f
-- title:
--   Equations (1)–(3), pp. 9–10 — the equation $rG(q)=k$ has a solution $q\ge 0$ for every $0<k\le r$
-- statement:
--   Let $M$ be a standard model (Assumptions 1–3, a continuous probability density $f$ that is positive on its support $[0,\bar a)$ and has finite mean, increasing generalized failure rate). Write $\bar F(q)=\int_q^\infty f$ for the survival function and
--   $$G(q)=\bar F(q)-q f(q).$$
--   Then for every level $k$ with $0<k\le r$ there is a $q\ge 0$ with
--   $$r\,G(q)=k.$$
--
--   The paper defines $\tilde q$, $q^o$ and $\hat q^*$ as the solutions of (1) $rG(q)=c+(1-p)s$, (2) $rpG(q)=c$ and (3) $rG(q)=s$ (the last when $s\le r$). This lemma says those solutions exist, which the paper takes for granted. Levels $c+(1-p)s$ (when it is at most $r$), $c/p$ and $s$ (when $s\le r$) all lie in $(0,r]$ by Assumption 1.
-- source:
--   Farahani, Dawande, Gurnani & Janakiraman, Better to bend than to break: sharing supply risk using the supply-flexibility contract (SSRN 3143238; M&SOM 23(5) 2021), p. 9 eq. (1) and p. 10 eqs. (2)–(3): existence of the solutions q̃, q°, q̂* (presupposed in the paper)

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_SupplyFlex_SupplierLed_Setting

namespace SupplyFlex.SupplierLed

/-- Equations (1)–(3), pp. 9–10: for every level `0 < k ≤ r` the equation `r G(q) = k` has a
solution `q ≥ 0`. -/
theorem root_G_exists (M : Model) (hM : M.Std) (k : ℝ) (hk0 : 0 < k) (hkr : k ≤ M.r) :
    ∃ q : ℝ, 0 ≤ q ∧ M.r * G M.f q = k := by sorry

end SupplyFlex.SupplierLed
