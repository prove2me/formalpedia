-- Prove2me | Theorems.Thm_TimeSpaceMA_lemma_A_5
-- name    : TimeSpaceMA.lemma_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:57:29.308191+00:00
-- url     : https://prove2.me/theorems/80e21bef-5451-4821-b113-178f63b3bb96
-- title:
--   Lemma A.5 — derandomized amplification
-- statement:
--   Let $\mu\ge1$ and $\rho=2^{-c}$ for a nonnegative integer $c$. There is a list of $M=O(\mu^2/\rho)$ strings $a_1,\dots,a_M\in\{0,1\}^\mu$ such that for every deterministic algorithm $A$ on $\{0,1\}^\mu$: if $A$ rejects a uniform $z$ with probability at least $\rho$, then the procedure that samples a uniform $z$, runs $A(z\oplus a_i)$ for every $i$, and accepts iff all runs accept, rejects with probability at least $2/3$.
--
--   If $A$ accepts every input, so does the procedure, and the procedure uses $\mu$ random bits. Each $a_i$ is computable in $\mu\,\mathrm{polylog}(\mu/\rho)$ time and $\mathrm{polylog}(\mu/\rho)$ space.
--
--   Differences from the source:
--   - generalization: each a_i computed in µ polylog(µ/ρ) time and polylog(µ/ρ) space → one coin-free RAM program on [µ, c, i, j] returning bit j of a_i at cost C₁(log₂(µ/ρ) + 2)^K; reason: summing over j gives the printed time; on a log-cost RAM a touched cell costs work, so the printed space follows
--   - encoding: the procedure uses µ random bits → z ranges over Fin µ → Bool; reason: that is what µ bits are
--   - encoding: a deterministic algorithm A → any function A : {0,1}^µ → Bool (true is accept); reason: the page uses only the rejected set of A
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Lemma A.5, p.37

import Definitions.Def_TimeSpaceMA_RAM

namespace TimeSpaceMA

open Classical in
/-- **Lemma A.5** (Derandomized amplification; Williams, Xi, STOC 2027 submission, manuscript sha256
184c2f95…, p.37). For `µ ≥ 1` and `ρ = 2^{−c}` there is a list of `M = O(µ²/ρ)` strings `a_i ∈ {0,1}^µ` such
that for every deterministic `A`: if `A` rejects a uniform `z` with probability at least `ρ`, then the
procedure "sample `z`, run `A(z ⊕ a_i)` for every `i`, accept iff all accept" rejects with probability at
least `2/3`; and if `A` accepts every input, so does the procedure. Each `a_i` is computable in
`µ polylog(µ/ρ)` time and `polylog(µ/ρ)` space.

**Formalization Note** `A` is any function (`true` is accept). The computation clause is per bit: one
coin-free program on start memory `[µ, c, i, j]` halts with `M[0]` the bit `j` of `a_i`, at cost at most
`C₁ (log₂(µ/ρ) + 2)^K`. Summing over `j` gives the printed time, and since each touched cell costs work on a
log-cost RAM, the printed space follows too (`generalization`). -/
theorem lemma_A_5 :
    ∃ (C₀ C₁ : ℝ) (K : ℕ) (P : Program), 0 < C₀ ∧ 0 < C₁ ∧ P.CoinFree ∧
      ∀ μ c : ℕ, 1 ≤ μ →
        let ρ : ℝ := (2 : ℝ)⁻¹ ^ c
        ∃ (M : ℕ) (a : Fin M → Fin μ → Bool),
          (M : ℝ) ≤ C₀ * (μ : ℝ) ^ 2 / ρ ∧
          (∀ A : (Fin μ → Bool) → Bool,
            (ρ ≤ ((Finset.univ.filter fun z => A z = false).card : ℝ) / (2 : ℝ) ^ μ →
              (2 : ℝ) / 3 ≤
                ((Finset.univ.filter fun z : Fin μ → Bool =>
                    ∃ i, A (fun k => xor (z k) (a i k)) = false).card : ℝ) / (2 : ℝ) ^ μ) ∧
            ((∀ z, A z = true) → ∀ (z : Fin μ → Bool) (i : Fin M),
              A (fun k => xor (z k) (a i k)) = true)) ∧
          ∀ (i : Fin M) (j : Fin μ),
            ∃ st, P.RunsTo zeroTape (memOf [μ, c, i.val, j.val]) st ∧
              (st.work : ℝ) ≤ C₁ * (Real.logb 2 ((μ : ℝ) / ρ) + 2) ^ K ∧
              st.mem 0 = (a i j).toNat := by sorry

end TimeSpaceMA
