-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P44_wholeCodeword_markov
-- name    : QAlgorithms.Papers.Independent.Next46.P44.wholeCodeword_markov
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:56:09.99375+00:00
-- url     : https://prove2.me/theorems/a6737334-070f-4ac2-8a52-9e9a0f0d9f53
-- title:
--   Whole-codeword Markov property of the executed feedback protocol
-- statement:
--   Let $n\ge1$. Let $S$, $A$, $H$, and $K$ be nonempty finite alphabets indexing respectively source letters, classical code letters, a basis of the physical channel space, and feedback outcomes. The finite source has consistent normalized block laws $p_n$ satisfying the asymptotic equipartition property, with base-two surprisal converging in probability to its entropy rate. Let $c:S^n\to A^n$ be a deterministic encoder. To each used codeword $a=c(m)$ assign an arbitrary density matrix $\rho_a$ on $H^{\otimes n}$; its factors may be entangled.
--
--   Fix the source's feedback protocol: each round applies the same CPTP channel to the next designated input factor, measures only the already received factors, and sends the outcome noiselessly to the sender, whose outcome-selected CPTP response acts only on the remaining untransmitted factors. All these operations are fixed independently of the message and codeword. Initially the sender holds all input factors and there is no shared resource. Let $\sigma_a$ be the receiver state obtained by executing this protocol from $\rho_a$, retaining an orthogonal classical record of every feedback outcome. The execution uses subnormalized branches, including zero-probability histories, and does not divide by branch probabilities. Form the actual joint state
--
--   $$
--   \Omega_{MAZ}=\sum_{m\in S^n}p_n(m)\,|m\rangle\langle m|\otimes|c(m)\rangle\langle c(m)|\otimes\sigma_{c(m)}.
--   $$
--
--   Then the whole classical codeword separates the message from the terminal receiver:
--
--   $$
--   I(M:Z\mid A)_\Omega=S(\Omega_{MA})+S(\Omega_{AZ})-S(\Omega_A)-S(\Omega_{MAZ})=0.
--   $$
--
--   Entropies are in bits. This is the full-codeword Markov property asserted in the paper. It does not give a Markov property conditioned on a codeword prefix, which would require an additional preparation restriction.
-- source:
--   Classical feedback for quantum channels, arXiv:quant-ph/0409207v3, PDF p. 6, §2, paragraph continuing PDF p.5

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P44

open scoped Matrix ComplexConjugate

open Filter

/-- Skeen, quant-ph/0409207v3, PDF p.6 (paragraph continuing p.5): the whole-codeword
classical-quantum Markov chain M_1^n -> A_1^n -> Z_1^n. The source is finite-alphabet
and AEP (p.3); codeword states are normalized and may be entangled (pp.2-4).
The terminal receiver includes all feedback records. This asserts no prefix Markov
property and no directed data-processing inequality. -/
theorem wholeCodeword_markov {n : ℕ} (hn : 0 < n)
    {S A H K : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype H] [DecidableEq H] [Nonempty H]
    [Fintype K] [DecidableEq K] [Nonempty K]
    (src : FiniteAEPSource S) (c : (Fin n → S) → (Fin n → A))
    (rho : (Fin n → A) → Matrix (Fin n → H) (Fin n → H) ℂ)
    (hrho : ∀ m, IsDensityMatrix (rho (c m))) (C : FeedbackProtocol n H K) :
    conditionalInfo (terminalState src c rho C) = 0 := by sorry

end QAlgorithms.Papers.Independent.Next46.P44

end
