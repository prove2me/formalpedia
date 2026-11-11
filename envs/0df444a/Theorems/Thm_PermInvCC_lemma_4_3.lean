-- Prove2me | Theorems.Thm_PermInvCC_lemma_4_3
-- name    : PermInvCC.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:26:35.854022+00:00
-- url     : https://prove2.me/theorems/e43744b2-d4dd-44da-b628-e05e041f4f05
-- title:
--   Lemma 4.3 — uniform polynomial approximation of type-averaged acceptance
-- statement:
--   Fix an integer $q\ge2$ and $\beta>0$. There is $K_{q,\beta}>0$, depending only on $q$ and $\beta$, such that the following holds. Fix a total length $N\ge1$, row and column margins $\rho,\sigma$ of total $N$ over $[q]$, and a connected spanning bipartite subgraph $G$ on the active symbols. For any protocol using at most $c$ qubits with prior entanglement on $[q]^N\times[q]^N$, let $p(S)$ be its acceptance probability averaged uniformly over all input pairs of joint type $S$. For each $\varepsilon\in(0,1)$ there is a single real polynomial $P$ in the entries of $S$, of total degree at most
--   $$K_{q,\beta}\bigl(c+\log(1/\varepsilon)\bigr),$$
--   such that $|p(S)-P(S)|\le\varepsilon$ for every integer type $S$ with the fixed margins satisfying $S_e\ge\beta N$ for every $e\in G$. Entries outside $G$ may be zero.
--
--   One polynomial controls a whole interval of types, including types outside any promise.
--
--   Differences from the source:
--   - encoding: margins with at most q active symbols per side → margins over the alphabet Fin q; reason: inactive symbols never occur; relabelling the active symbols into [q] gives the general case
--   - encoding: logarithms base two → Real.logb 2; reason: Lean notation; same values
--   - reading: arbitrary prior entanglement → an arbitrary input-independent unit start state on finitely many qubits W (W unbounded); reason: the standard finite-dimensional model of entanglement-assisted communication, the one of [LS09] and [SS24, Thm 2.22] on which the paper builds its quantum bounds (App. B.3); the paper never uses an infinite-dimensional state
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Lemma 4.3, p.16 (proof pp.44–45)

import Mathlib
import Definitions.Def_PermInvCC_jointType
import Definitions.Def_PermInvCC_IsConnSpanning
import Definitions.Def_PermInvCC_EntQProtocol
import Definitions.Def_PermInvCC_typeAvgAccept

namespace PermInvCC

/-- **Lemma 4.3 (Uniform Polynomial Approximation)** (Y. Huang and Z. Ye, arXiv:2609.40116, held
version sha256 fe1797dd…, p.16). Fix an integer `q ≥ 2`, `β > 0`, total length `N ≥ 1`, and row
and column margins with at most `q` active symbols per side. Let `G` be a connected spanning
bipartite subgraph on the active symbols. For any `c`-qubit protocol with prior entanglement, let
`p(S)` denote its acceptance probability averaged uniformly over all input pairs of joint type `S`.
For each `ε ∈ (0, 1)`, there is a single real polynomial `P` in the entries of `S`, of total
degree at most `K_{q,β}(c + log(1/ε))`, such that `|p(S) − P(S)| ≤ ε` for every integer type with
the fixed margins satisfying `S_e ≥ βN` for every `e ∈ G`. Entries outside `G` may be zero. Here
`K_{q,β} > 0` depends only on `q` and `β`.

**Formalization Note.** The alphabet is `[q]`, covering "at most `q` active symbols per side".
`K` is chosen after `q, β` and before `N`, the margins, `G`, the protocol and `ε`; the polynomial
is chosen after the protocol and `ε` and before `S`. Logs are base two. -/
theorem lemma_4_3 (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ ρ σ : Fin q → ℕ, ∑ a, ρ a = N → ∑ b, σ b = N →
        ∀ G : Finset (Fin q × Fin q), IsConnSpanning ρ σ G →
          ∀ (c : ℕ) (P : EntQProtocol (Fin N → Fin q) (Fin N → Fin q)), P.cost ≤ c →
            ∀ ε : ℝ, 0 < ε → ε < 1 →
              ∃ Pol : MvPolynomial (Fin q × Fin q) ℝ,
                (Pol.totalDegree : ℝ) ≤ K * ((c : ℝ) + Real.logb 2 (1 / ε)) ∧
                ∀ S : Fin q → Fin q → ℕ, rowMargin S = ρ → colMargin S = σ →
                  (∀ e ∈ G, β * N ≤ (S e.1 e.2 : ℝ)) →
                  |typeAvgAccept P S - MvPolynomial.eval (fun e => (S e.1 e.2 : ℝ)) Pol| ≤ ε := by sorry

end PermInvCC
