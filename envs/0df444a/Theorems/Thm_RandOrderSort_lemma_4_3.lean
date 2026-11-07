-- Prove2me | Theorems.Thm_RandOrderSort_lemma_4_3
-- name    : RandOrderSort.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:50.143195+00:00
-- url     : https://prove2.me/theorems/92113fda-0cad-4e8b-9c19-d2df230f8d3e
-- title:
--   Lemma 4.3 — reallocation requests after a growing phase
-- statement:
--   Let $n\ge 8192$ and let $P_j$ be the prefix set observed before growing phase $j$ begins. The phase-$j$ tree has boundaries every $T$ prefix ranks and capacity $2T$ per bucket. At the following reallocation, let $I$ be an interval of the extended key order and put $Z(I)=|P_j\cap I|$. The number of old empty-cell requests canonical in $I$ is at most
--   $$2Z(I)+4T.$$
--
--   Reallocation demand after a growing phase is therefore controlled by the old prefix alone, whatever the placements were.
--
--   Differences from the source:
--   - generalization: I a node interval of any new partition tree → I any interval of the extended key order, with endpoints e₁, e₂; reason: every node interval of every partition tree is such an interval, so the Lean statement specializes to the page's
--   - encoding: an old empty-cell request canonical in I → a logged request of the following reallocation whose old label lies in I; reason: the page's proof: "A surviving cell's request is canonical in I exactly when its old label lies in I"
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Lemma 4.3, p.22, display (23)

import Mathlib
import Definitions.Def_RandOrderSort_empiricalSort
import Definitions.Def_RandOrderSort_Dop

namespace RandOrderSort

/-- **Lemma 4.3 (Reallocation requests after a growing phase)**, Kang, Fan, *Optimal High Probability Bounds for Random Order Online Sorting*, arXiv:2610.15438 (version of 2026-11-01), p.22: "Let P_j be the prefix
set observed before growing phase j begins. The phase-j tree has boundaries every T prefix ranks and
capacity 2T per bucket. At the following reallocation, let I be a node interval of any new partition
tree and put Z(I) = |P_j ∩ I|. The number of old empty-cell requests canonical in I is at most
2Z(I) + 4T. (23)"

**Formalization Note.** For `n ≥ 8192`, every execution and every growing phase `j ≤ J`; the
following reallocation is that of phase `j + 1` (the first shrinking phase when `j = J`). `I` is any
interval of the extended key order with endpoints `e₁, e₂` (left-closed, right-open, `+∞` included
when `e₂ = +∞`), which contains every node interval of every partition tree; an old request is
canonical in `I` when its old label lies in `I`. Boundary ranks are 1-based. -/
theorem lemma_4_3 : ∀ n, 16 * T ≤ n → ∀ (x : Fin n → ℝ) (π σ : Equiv.Perm (Fin n)), ∀ j ≤ J n,
    (∀ ℓ ∈ Finset.Ico 1 (2 ^ j),
      rankIn (ltOf x π σ) (Finset.range (tj j)) ((phaseTree n (ltOf x π σ) j).bd ℓ) + 1 = T * ℓ) ∧
    (∀ ℓ, phaseCap n j ℓ = 2 * T) ∧
    ∀ e₁ e₂ : Ext,
      ((opReqs (runOf x π σ) (j + 1) false).filter (fun r => inIvl (ltOf x π σ) e₁ e₂ r.y)).length ≤
        2 * ((Finset.range (tj j)).filter (fun a => inIvl (ltOf x π σ) e₁ e₂ (.key a) = true)).card +
          4 * T := by sorry

end RandOrderSort
