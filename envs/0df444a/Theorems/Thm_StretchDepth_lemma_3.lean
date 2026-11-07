-- Prove2me | Theorems.Thm_StretchDepth_lemma_3
-- name    : StretchDepth.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:05:59.844106+00:00
-- url     : https://prove2.me/theorems/8447012f-ca23-4c87-98ed-9a45ac7ec1c0
-- title:
--   Lemma 3 — nonnegative signed advantage, $\epsilon^2$ and $3q+1$ queries
-- statement:
--   Let $N>n$, $M>m$ and $0<\gamma,\epsilon\le1$, and let $H$ be a query procedure and $R$ a randomized query procedure with
--   $$
--   \mathrm{Adv}_{H^G}(T)\ge\gamma\implies|\mathrm{SAdv}_G(R^{G,T})|\ge\epsilon\qquad\text{for all }G,T.
--   $$
--   Then there is a randomized query procedure $\tilde R$ such that for all $G,T$:
--
--   1. $\mathrm{SAdv}_G(\tilde R^{G,T})\ge0$;
--   2. $\mathrm{Adv}_{H^G}(T)\ge\gamma$ implies $\mathrm{SAdv}_G(\tilde R^{G,T})\ge\epsilon^2$;
--   3. if $R$ makes at most $q$ queries in total, then $\tilde R$ makes at most $3q+1$ queries in total.
--
--   This allows the proof of Theorem 1 to argue with signed advantages, where an averaging argument is available.
--
--   Differences from the source:
--   - encoding: a randomized query procedure with q queries on every input and all randomness → a PMF over functions to decision trees, with the bound on real pairs (G, T) and on the support; reason: the procedures with at most q queries form a finite set after pruning unreachable branches, and only runs on real pairs matter to the definition
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), Lemma 3, p.18

import Definitions.Def_StretchDepth_IsPRGReduction

namespace StretchDepth

/-- **Lemma 3 ([BG11]): passing to nonnegative signed advantage.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), Lemma 3, p.18: "Suppose (H, R) is an amplification reduction such that, for every G, T it
holds that AdvHG(T) ≥ γ =⇒ AdvG(RG,T ) ≥ ϵ. Then there is an amplification reduction (H, ˜R) such
that SAdvG( ˜RG,T ) ≥ 0 for all G, T, and AdvHG(T) ≥ γ =⇒ SAdvG( ˜RG,T ) ≥ ϵ2. If R makes at most q
queries in total (to G and T), then ˜R makes at most 3q + 1 queries in total."

**Formalization Note.** The conditions of Definition 3 on the parameters are hypotheses. The query
clause holds for every `q`. `H` is unchanged, so its bounds as a construction are unchanged. -/
theorem lemma_3 {n N m M : ℕ} (hN : n < N) (hM : m < M) (γ ε : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (H : Bits m → RoundTree n N M)
    (R : PMF (Bits N → QProc n N M))
    (hR : ∀ (G : Bits n → Bits N) (T : Bits M → Bool), γ ≤ advH H G T → ε ≤ |SAdv R G T|) :
    ∃ Rt : PMF (Bits N → QProc n N M),
      (∀ (G : Bits n → Bits N) (T : Bits M → Bool), 0 ≤ SAdv Rt G T) ∧
      (∀ (G : Bits n → Bits N) (T : Bits M → Bool), γ ≤ advH H G T → ε ^ 2 ≤ SAdv Rt G T) ∧
      ∀ q : ℕ, WithinQueries R q → WithinQueries Rt (3 * q + 1) := by sorry

end StretchDepth
