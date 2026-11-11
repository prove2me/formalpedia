-- Prove2me | Theorems.Thm_SwitchingStable_Universal_lemma_2
-- name    : SwitchingStable.Universal.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:18.969736+00:00
-- url     : https://prove2.me/theorems/572a62db-f2bc-4c74-8508-2f44b42d87e4
-- title:
--   Lemma 2 — Alternating-cycle preferences and stable-partner comparisons
-- statement:
--   Let $\mu,\nu$ be stable matchings of a complete strict market. On every nontrivial alternating cycle all men prefer the same matching and all women prefer the other. If $u$ has stable list $v_0\succ_u\cdots\succ_u v_{d-1}$ and $\mu(u)=v_q$, then
--   $$r<q\Longrightarrow\mu(v_r)\succ_{v_r}u,\qquad r>q\Longrightarrow u\succ_{v_r}\mu(v_r).$$
--   Here the partner of a woman means the inverse matching. Both the cycle statement and the stable-partner comparisons are retained; they supply the structural comparisons used by later witnesses.
--
--   Differences from the source:
--   - encoding: Alternating cycles in the symmetric difference of two matchings → Orbits of the permutation taking each man through one matching and back through the other; reason: These orbits are precisely the nontrivial alternating cycles; both sides retain separate preference functions.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), p. 3, PDF p. 4, Lemma 2

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Transport

namespace SwitchingStable.Universal

open MeasureTheory

theorem lemma_2 {n : ℕ} (I : StableMatching.Instance n)
    (μ ν : StableMatching.Matching n) (hμ : I.IsStable μ) (hν : I.IsStable ν) :
    (∀ a : Fin n, μ a ≠ ν a →
      ((∀ b : Fin n, (∃ k : ℕ, (μ.trans ν.symm)^[k] a = b) →
        I.manPrefers b (μ b) (ν b) ∧ I.womanPrefers (μ b) (ν.symm (μ b)) b) ∨
       (∀ b : Fin n, (∃ k : ℕ, (μ.trans ν.symm)^[k] a = b) →
        I.manPrefers b (ν b) (μ b) ∧ I.womanPrefers (μ b) b (ν.symm (μ b))))) ∧
    (∀ (u : Fin n) (r : ℕ), r < degree I u →
      (r < idx I μ u → I.womanPrefers (atPartner I μ u r) (μ.symm (atPartner I μ u r)) u) ∧
      (idx I μ u < r → I.womanPrefers (atPartner I μ u r) u (μ.symm (atPartner I μ u r)))) := by sorry

end SwitchingStable.Universal
