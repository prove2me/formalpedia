-- Prove2me | Theorems.Thm_RoundedPotentials_Main_Supplement_corollary_4_3
-- name    : RoundedPotentials.Main.Supplement.corollary_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:07:15.267049+00:00
-- url     : https://prove2.me/theorems/b2c56664-8293-4521-bf90-1804c87691c8
-- title:
--   Corollary 4.3 — Certificate-first streaming
-- statement:
--   Let $n\ge2$, $W\ge1$, terminals $s\ne t$ and an integer $p$ be public. Consider an arbitrary-order stream of directed loopless items $(u,v,c)$ with $c\in\mathbb N$, several of which may concern the same ordered pair, such that the total capacity on each ordered pair is at most $W$.
--
--   There is a constant $C$, independent of $n,W,s,t,p$, such that the predicate $\mathrm{MaxFlow}(s,t)=p$ of the final network has a deterministic one-pass certificate-first verifier with the following properties.
--
--   1. **Perfect soundness.** For every stream and every certificate, if the verifier accepts then $\mathrm{MaxFlow}(s,t)=p$.
--   2. **Perfect completeness, independent of the order.** For every capacity matrix with $\mathrm{MaxFlow}(s,t)=p$ there is one certificate of at most $Cn(\lfloor\log_2(nW)\rfloor+1)$ bits that is accepted on every stream, in every order, whose totals are that matrix.
--   3. **Working space.** On every stream and with every certificate, the working memory never exceeds $Cn(\lfloor\log_2(nW)\rfloor+1)$ bits. The certificate lies in read-only memory and is not counted as working space.
--
--   Together with Theorem 4.1, this gives the second, certificate-first clause of Theorem 1.3.
--
--   **Formalization Note** The model is `CertFirstVerifier`: a bit-string working memory with arbitrary transitions, each of which may read the whole certificate. This is the read-only random-access certificate of [DFPR25].
--
--   Differences from the source:
--   - encoding: deterministic one-pass verifier in the certificate-first model of [DFPR25] → CertFirstVerifier: bit-string working memory, arbitrary (non-uniform) transitions that may read the whole certificate, one verifier per public (n, W, s, t, p); reason: the model charges certificate and working-space bits, as [DFPR25] does
--   - encoding: directed edges → stream items on ordered pairs of distinct vertices; reason: §2 graphs are loopless
--   - encoding: O(n log(nW)) bits → C·n·(⌊log₂(nW)⌋+1) with one constant C for all n, W, s, t, p; reason: explicit form of the O-bound; n ≥ 2 so the logarithm is positive
--   - encoding: integer p → p ∈ ℤ; for p < 0 the predicate is false and soundness forces rejection; reason: same instances
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), p. 19, Corollary 4.3

import Mathlib
import Definitions.Def_RoundedPotentials_Main_Supplement_Streaming

namespace RoundedPotentials.Main.Supplement

open RoundedPotentials.Main

theorem corollary_4_3 : ∃ C : ℕ,
    ∀ (n W : ℕ), 2 ≤ n → 1 ≤ W → ∀ (s t : Fin n), s ≠ t → ∀ p : ℤ,
      ∃ V : CertFirstVerifier n,
        -- perfect soundness, for every certificate and every stream order
        (∀ (σ : List (Contribution n)), ContributionPromise W σ → ∀ z : List Bool,
          V.accepts z σ = true → MatrixMaxValue n W (aggCap σ) s t p) ∧
        -- perfect completeness with one certificate for every order of the graph's stream
        (∀ (cap : Fin n → Fin n → ℕ), (∀ u v, cap u v ≤ W) →
          MatrixMaxValue n W cap s t p →
          ∃ z : List Bool, z.length ≤ C * n * (Nat.log 2 (n * W) + 1) ∧
            ∀ σ : List (Contribution n), ContributionPromise W σ →
              (∀ u v, u ≠ v → aggCap σ u v = cap u v) → V.accepts z σ = true) ∧
        -- working space
        (∀ (σ : List (Contribution n)), ContributionPromise W σ → ∀ z : List Bool,
          ∀ mem ∈ V.memories z σ, mem.length ≤ C * n * (Nat.log 2 (n * W) + 1)) := by sorry

end RoundedPotentials.Main.Supplement
