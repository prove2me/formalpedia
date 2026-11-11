-- Prove2me | Theorems.Thm_PermInvCC_lemma_B_2
-- name    : PermInvCC.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:27:59.516054+00:00
-- url     : https://prove2.me/theorems/59d0846d-1e18-4202-aeca-0ce87d10634d
-- title:
--   Lemma B.2 — exponential contraction $\|B_S(I-P_{X,d})\|_{2\to2}\le K^{op}_{q,\beta}e^{-\gamma_{q,\beta}d}$
-- statement:
--   Fix an integer $q\ge2$ and $\beta>0$. There are constants $K^{op}_{q,\beta}\ge1$ and $\gamma_{q,\beta}>0$ such that the following holds, uniformly over $N$, the margins, and eligible $S,G$. Let $S$ be a type of total $N\ge1$ over the alphabet $[q]$ with margins $\rho,\sigma$, and suppose there is a connected spanning bipartite subgraph $G$ on its active row and column symbols with
--   $$S_e\ge\beta N\qquad(e\in G). \tag{B.3}$$
--   Let $X=X_\rho$, $Y=X_\sigma$ with their uniform probability measures. Then for every integer $d\ge0$
--   $$\|B_S(I-P_{X,d})\|_{2\to2}\le K^{op}_{q,\beta}\,e^{-\gamma_{q,\beta}d}. \tag{B.4}$$
--
--   It is the analytic core of the uniform polynomial approximation, Lemma 4.3.
--
--   Differences from the source:
--   - encoding: operator norm ‖B_S(I − P_{X,d})‖_{2→2} → ‖B_S h‖_{L²(Y)} ≤ K e^{−γd} ‖h‖_{L²(X)} for every h ∈ V_{X,>d}; reason: I − P_{X,d} is the orthogonal projection onto V_{X,>d}, which does not increase norms, so the two forms are equivalent
--   - encoding: a type with at most q active symbols on each side → a table over the alphabet Fin q; reason: inactive symbols never occur in the multislices; relabelling the active symbols into [q] gives the general case
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Lemma B.2, eqs. (B.3)–(B.4), p.41

import Mathlib
import Definitions.Def_PermInvCC_jointType
import Definitions.Def_PermInvCC_IsConnSpanning
import Definitions.Def_PermInvCC_multislice
import Definitions.Def_PermInvCC_Vgt
import Definitions.Def_PermInvCC_BS

namespace PermInvCC

/-- **Lemma B.2** (Y. Huang and Z. Ye, arXiv:2609.40116, held version sha256 fe1797dd…, p.41).
Fix an integer `q ≥ 2` and `β > 0`. Suppose a type `S` of total `N ≥ 1`, with at most `q` active
symbols on each side, has a connected spanning bipartite subgraph `G` on its active row and column
symbols such that `S_e ≥ βN` for every `e ∈ G` (B.3). Then there are constants `K^op_{q,β} ≥ 1`
and `γ_{q,β} > 0` such that, for every integer `d ≥ 0`, `‖B_S(I − P_{X,d})‖_{2→2} ≤ K^op_{q,β}
e^{−γ_{q,β} d}` (B.4). The constants are uniform over `N`, the margins, and eligible `S, G`.

**Formalization Note.** The alphabet is `[q]` (`Fin q`), which covers "at most `q` active
symbols" (inactive symbols never occur in the multislices). `X = X_ρ`, `Y = X_σ` for the margins
`ρ, σ` of `S`, with the **uniform probability** `L²` norms. (B.4) is stated in the equivalent
form `‖B_S h‖_{L²(Y)} ≤ K e^{−γd} ‖h‖_{L²(X)}` for every `h ∈ V_{X,>d}`: `I − P_{X,d}` is the
orthogonal projection onto `V_{X,>d}`. -/
theorem lemma_B_2 (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) :
    ∃ K γ : ℝ, 1 ≤ K ∧ 0 < γ ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ S : Fin q → Fin q → ℕ, ∑ a, ∑ b, S a b = N →
        ∀ G : Finset (Fin q × Fin q), IsConnSpanning (rowMargin S) (colMargin S) G →
          (∀ e ∈ G, β * N ≤ (S e.1 e.2 : ℝ)) →
          ∀ (d : ℕ) (h : (Fin N → Fin q) → ℝ), h ∈ Vgt (multislice N (rowMargin S)) d →
            msNorm (multislice N (colMargin S)) (BS S h) ≤
              K * Real.exp (-γ * d) * msNorm (multislice N (rowMargin S)) h := by sorry

end PermInvCC
