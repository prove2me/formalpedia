-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P80_exponentialStrongConverse
-- name    : QAlgorithms.Papers.Independent.Information100.P80.exponentialStrongConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:15:03.643104+00:00
-- url     : https://prove2.me/theorems/56d6723f-99a5-492a-9688-341abca9944e
-- title:
--   Theorem 1 (Exponential strong converse)
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel between positive finite-dimensional registers. Let $Q(\mathcal N)$ be its unassisted operational quantum capacity, defined using entanglement-transmission codes with fidelity tending to one and lower limiting rate at least the claimed rate. All logarithms are base two. For every $\gamma>0$, there are constants $\alpha>0$ and $n_0\ge1$, depending only on the channel and $\gamma$, such that every $n\ge n_0$ and every entanglement-generation code of positive integer dimension $M$ obey
--
--   $$
--   \frac{\log_2 M}{n}\ge Q(\mathcal N)+\gamma
--   \quad\Longrightarrow\quad
--   F<2^{-\alpha n}.
--   $$
--
--   Here a generation code consists of an arbitrary normalized mixed state on $R\otimes A^{\otimes n}$, with $\dim R=M$, and an arbitrary joint CPTP decoder $B^{\otimes n}\to\widehat L$, with $\dim\widehat L=M$. The reference is untouched, and $F$ is the overlap of the decoded state with the normalized maximally entangled target on $R\widehat L$. There is no prescribed reference marginal and no preshared entanglement or auxiliary communication.
--
--   This gives exponential decay of squared entanglement fidelity above quantum capacity. The uniform eventual formulation is explicit in the proof on PDF pp.10–11 and implies the printed statement for every code sequence.
-- source:
--   Strong Converses for Quantum Channel Capacities from Blowing-Up Lemmata, arXiv:2609.11771v1, PDF p. 2, Theorem 1 (Exponential strong converse)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P80

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

/-- Theorem 1, PDF p.2; the uniform threshold is explicit in its proof on pp.10–11.
The bound includes arbitrary normalized mixed generation inputs. -/
theorem exponentialStrongConverse
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N)
    (gamma : ℝ) (hgamma : 0 < gamma) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n ≥ n0, ∀ C : GenerationCode (Fin n → A) (Fin n → B),
        quantumCapacity N + gamma ≤ log2 (C.M : ℝ) / (n : ℝ) →
        generationFidelity (piSuperop (fun _ : Fin n => N)) C <
          (2 : ℝ) ^ (-alpha * (n : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P80

end
