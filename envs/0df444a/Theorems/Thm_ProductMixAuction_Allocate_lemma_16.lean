-- Prove2me | Theorems.Thm_ProductMixAuction_Allocate_lemma_16
-- name    : ProductMixAuction.Allocate.lemma_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:08.451552+00:00
-- url     : https://prove2.me/theorems/c4b4fa96-5047-4cec-a970-ade70535ce44
-- title:
--   Lemma 16, p. 21 — projecting a bid list w.r.t. p keeps D(p) and makes a locally valid list 1/2-valid
-- statement:
--   Let $\mathcal B$ be a bid list and $p$ a price. For each bid $b$ with demanded goods $I$ at $p$, its *projection* w.r.t. $p$ is $b'=b-e^{[n]_0\setminus I}$ if $0\in I$ and $b'=b+e^I$ otherwise; let $\mathcal B'$ be the list of projections. Then
--   $$D_{\mathcal B'}(p)=D_{\mathcal B}(p),$$
--   and if $\mathcal B$ is locally valid at $p$, then $\mathcal B'$ is $\tfrac12$-valid at $p$, i.e. $f_{\mathcal B'}$ is convex on $B(p;\tfrac12)$.
--
--   Projection widens every surplus gap by $1$ without changing demand at $p$; ShiftProjectUnshift uses it to make the effect of the shift robust before the shift is undone.
--
--   Differences from the source:
--   - reading: the projected bid list is locally 1/2-valid → the projected list is 1/2-valid at p (f convex on B(p; 1/2)); reason: 'locally ε-valid' is not defined separately; the proof derives ε-validity at p from Lemma 9 and Observation 15
--   - generalization: bid vectors integral (§2.2, p. 9) or in ℤ + {0, 1/10} (Definition 4) with reject entry b₀ = 0 → arbitrary real bid vectors over [n]₀, the reject entry v 0 unconstrained; reason: the proof never uses integrality; a bid with reject entry c has the same demanded goods as b − c·e^{[n]₀} and adds the constant w(b)·c to f_ℬ, so the statement for b₀ = c is the statement for b₀ = 0; the paper's bids are instances
-- source:
--   Baldwin, Goldberg, Klemperer, Lock, Solving Strong-Substitutes Product-Mix Auctions, arXiv:1909.07313v3, p. 21, Lemma 16

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Algorithm

namespace ProductMixAuction.Allocate

theorem lemma_16 {n : ℕ} (B : List (Bid n)) (p : Fin n → ℝ) :
    demand (B.map fun b => project b p) p = demand B p ∧
      (LocallyValid B p → EpsValid (B.map fun b => project b p) p (1 / 2)) := by sorry

end ProductMixAuction.Allocate
