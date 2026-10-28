-- Prove2me | Theorems.Thm_PayAsBid_SoftReserve_lemma_1
-- name    : PayAsBid.SoftReserve.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:51.881787+00:00
-- url     : https://prove2.me/theorems/5dbda7b0-b098-4574-89cb-a4ca77052ae9
-- title:
--   Lemma 1, p. A1 — under an equitable rule with reserve r, equal prices ≤ r put everyone in, and a lowest price ≤ r is always in
-- statement:
--   For $n\ge1$ suppliers, let $q$ be an equitable (anonymous and monotone) assortment function with reserve price $r$: $q_i(b)=0$ whenever $b_i>r$, and the assortment is nonempty whenever some price is at most $r$. Then:
--
--   1. if every supplier prices identically $b\in[0,r]$, every supplier is in the assortment:
--   $$q(b,\dots,b)=(1,\dots,1);$$
--   2. for every $b\in\mathbb R^n_+$ and supplier $i$ with $b_i\le r$ and $b_i\le b_j$ for all $j\ne i$, we have $q_i(b)=1$.
--
--   The lemma says that an equitable rule cannot exclude the cheapest supplier, which pins down the assortment on many equilibrium price profiles.
--
--   **Formalization Note.** The hypothesis that the assortment is nonempty whenever some price is at most $r$ is the paper's "total demand must add up to one" (p. 8, and the proof of this lemma). Without it the statement is false: $q_i(b)=1[b_i\le t]$ with $t<r$ is anonymous, monotone and respects the reserve, but excludes everybody at equal prices in $(t,r]$.
-- source:
--   Choi, Saban & Weintraub, The Design of Optimal Pay-as-Bid Procurement Mechanisms, SSRN preprint 3785023 (version of 2022-12-08), p. A1 (PDF 34), Lemma 1

import Mathlib
import Definitions.Def_PayAsBid_SoftReserve_Model

namespace PayAsBid.SoftReserve

theorem lemma_1 {n : ℕ} (hn : 1 ≤ n) (q : AssortFn n) (r : ℝ) (hq : IsEquitable q)
    (hRP : ReserveRP1 q r) (hTD : TotalDemandOne q r) :
    (∀ b : ℝ, 0 ≤ b → b ≤ r → q (fun _ => b) = fun _ => true) ∧
    (∀ b : Fin n → ℝ, Nonneg b → ∀ i, b i ≤ r → (∀ j, j ≠ i → b i ≤ b j) → q b i = true) := by sorry

end PayAsBid.SoftReserve
