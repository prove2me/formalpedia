-- Prove2me | Theorems.Thm_PadicInt_nonempty_continuousMulEquiv_principalUnits
-- name    : PadicInt.nonempty_continuousMulEquiv_principalUnits
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:23:50.840058+00:00
-- url     : https://prove2.me/theorems/d6421314-e9de-486d-b536-7d45cf59e5c1
-- title:
--   Principal units of $\mathbb Z_p$ are topologically isomorphic to $\mathbb Z_p$ ($p$ odd)
-- statement:
--   Let $p$ be an odd prime and let
--   $$U_1=\{u\in\mathbb Z_p^\times : u\equiv 1 \pmod p\}=\ker\bigl(\mathbb Z_p^\times\to(\mathbb Z/p\mathbb Z)^\times\bigr)$$
--   be the group of principal units of the $p$-adic integers, with the topology induced from $\mathbb Z_p^\times$. Then $U_1$ is isomorphic, as a topological group, to the additive group $\mathbb Z_p$:
--   $$U_1\;\cong\;\mathbb Z_p .$$
--   (An explicit isomorphism is $a\mapsto(1+p)^a$.)
--
--   Together with the Teichmüller splitting $\mathbb Z_p^\times\cong\mu_{p-1}\times U_1$ this is the structure theorem for the unit group of $\mathbb Z_p$; it is the input needed to extract a $\mathbb Z_p$-quotient from the cyclotomic character, e.g. for the construction of the cyclotomic $\mathbb Z_p$-extension of $\mathbb Q$.
--
--   **Formalization Note** $U_1$ is written as the kernel of `Units.map PadicInt.toZMod`, and $\mathbb Z_p$ as `Multiplicative ℤ_[p]` so that the isomorphism is a `ContinuousMulEquiv`.
-- source:
--   J.-P. Serre, A Course in Arithmetic, GTM 7, Chapter II, §3.1, Proposition 8 (for p ≠ 2, U_1 ≅ Z_p via α ↦ (1+p)^α) and Theorem 2; see also Washington, Introduction to Cyclotomic Fields, 2nd ed., §5.1.

import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.ContinuousMonoidHom

theorem PadicInt.nonempty_continuousMulEquiv_principalUnits (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    Nonempty ((Units.map (PadicInt.toZMod (p := p)).toMonoidHom).ker ≃ₜ* Multiplicative ℤ_[p]) := by sorry
