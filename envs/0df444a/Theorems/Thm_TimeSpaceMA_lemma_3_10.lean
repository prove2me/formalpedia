-- Prove2me | Theorems.Thm_TimeSpaceMA_lemma_3_10
-- name    : TimeSpaceMA.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:30.357421+00:00
-- url     : https://prove2.me/theorems/632763e8-90a6-4887-af43-bb5d270303ba
-- title:
--   Lemma 3.10 = Theorem A.3 — a sparse systematic subset-sum code
-- statement:
--   For every integer $q\ge2$ there is a systematic subset-sum code $G$ of message length $q$ and block length $L\le q\,\mathrm{polylog}(q)$, such that the map $\ell\mapsto\mathrm{rep}(\ell)$ and all distinct supports are computable in $q\,\mathrm{polylog}(q)$ time, and such that:
--
--   1. the distinct supports have total size at most $L$;
--   2. for every abelian group $A$ and nonzero $z\in A^q$, the codeword $G(z)$ has at least $q=\delta L$ nonzero coordinates.
--
--   Differences from the source:
--   - encoding: polylog(q) → C(log₂ q + 2)^K with one C, K for all q; reason: the standard meaning
--   - encoding: computed in time q polylog(q) → one coin-free RAM program on [q], work bound as stated, final memory satisfying EncodesFamily; reason: the page names no machine or layout; the layout determines the map and the supports
--   - encoding: every abelian group → every abelian group in Lean's Type; reason: Type contains the groups Z^d, Q^d, Q/Z and the number fields that the paper uses
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Lemma 3.10, p.12; Theorem A.3, p.35

import Definitions.Def_TimeSpaceMA_RAM
import Definitions.Def_TimeSpaceMA_EncodesFamily
import Definitions.Def_TimeSpaceMA_polylogBound
import Definitions.Def_TimeSpaceMA_SubsetSumCode

namespace TimeSpaceMA

/-- **Lemma 3.10 = Theorem A.3** (Williams, Xi, STOC 2027 submission, manuscript sha256 184c2f95…, pp.12,
35). For every `q ≥ 2` there is a systematic subset-sum code of message length `q` and block length
`L ≤ q polylog(q)`, with the map `ℓ ↦ rep(ℓ)` and all distinct supports computable in `q polylog(q)` time,
such that (a) the distinct supports have total size at most `L`, and (b) every nonzero `z ∈ A^q`, over
every abelian group `A`, has a codeword with at least `q = δL` nonzero coordinates.

**Formalization Note** `polylog` is one `polylogBound C K`. The program is one coin-free RAM program with
start memory `[q]` and the output layout `EncodesFamily`. -/
theorem lemma_3_10 :
    ∃ (C : ℝ) (K : ℕ) (P : Program), 0 < C ∧ P.CoinFree ∧
      ∀ q : ℕ, 2 ≤ q →
        ∃ (L : ℕ) (G : SubsetSumCode q L) (σ : Fin q → Fin L),
          G.IsSystematic σ ∧
          (L : ℝ) ≤ q * polylogBound C K q ∧
          (∃ st, P.RunsTo zeroTape (memOf [q]) st ∧
            (st.work : ℝ) ≤ q * polylogBound C K q ∧ EncodesFamily st.mem G.supp) ∧
          distinctSize G.supp ≤ L ∧
          G.HasGroupDistance := by sorry

end TimeSpaceMA
