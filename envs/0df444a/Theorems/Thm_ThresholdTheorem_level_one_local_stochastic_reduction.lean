-- Prove2me | Theorems.Thm_ThresholdTheorem_level_one_local_stochastic_reduction
-- name    : ThresholdTheorem.level_one_local_stochastic_reduction
-- status  : Open
-- author  : @shivm
-- created : 2026-10-25T20:32:39.59824+00:00
-- url     : https://prove2.me/theorems/fdc59a1b-cc7b-4969-b8de-c2825a0c1c57
-- title:
--   Level reduction: one level of concatenation maps local stochastic noise of rate $e$ to rate $ce^2$
-- statement:
--   **Level reduction for one level of concatenation.** There are constants $c\ge 1$ and $A$, a block size $b$ and a block decoder $\mathrm{dec}:\{0,1\}^b\to\{0,1\}$ with the following property. Every layered circuit $C$ on any finite set of qubits $Q$ (gates $H,T,\mathrm{CNOT}$, preparations and waits) has a level-1 simulation $C'$ on $Q\times\{1,\dots,b\}$, with each logical qubit replaced by a block of $b$ physical qubits, such that $|C'|\le A\,|C|$. Moreover, for every rate $e\ge 0$ and every output distribution $P$ of $C'$ under local stochastic noise of rate $e$, the blockwise-decoded distribution is an output distribution of the *logical* circuit $C$ under local stochastic noise of rate $ce^2$:
--   $$P\in\mathcal N_{\mathrm{ls}}(C',e)\;\Longrightarrow\;\mathrm{dec}_*P\in\mathcal N_{\mathrm{ls}}(C,\,c\,e^2).$$
--   Here $\mathcal N_{\mathrm{ls}}(C,e)$ is the set of distributions `IsLocalStochasticDist C e`. A random fault set $F$ satisfies $\Pr[S\subseteq F]\le e^{|S|}$ for every set $S$ of locations, and faulty locations act by arbitrary channels on their qubits and a shared quantum environment.
--
--   This is the level-reduction lemma of Aliferis–Gottesman–Preskill. Replace each location by its fault-tolerant gadget (exRec) for a distance-3 code. A good exRec (at most one fault) acts as the ideal logical operation followed by an ideal decoder. A bad exRec needs two faults among $O(1)$ locations, so it becomes a faulty logical location, and bad sets have probability at most $(ce^2)^{|S|}$. Because the model has no intermediate measurements, the gadgets have to be measurement-free and use only fresh $|0\rangle$ preparations, as in Aharonov–Ben-Or. Iterating this lemma produces the level-$k$ concatenated simulation.
-- source:
--   P. Aliferis, D. Gottesman, J. Preskill, Quantum accuracy threshold for concatenated distance-3 codes, Quant. Inf. Comput. 6 (2006) 97-165, quant-ph/0504218, Sec. 5 (level reduction, local stochastic noise); D. Gottesman, arXiv:0904.2557, Sec. 5, proof of Theorem 10 (level reduction step); D. Aharonov, M. Ben-Or, Fault-tolerant quantum computation with constant error rate, SIAM J. Comput. 38 (2008), quant-ph/9906129 (fault tolerance without intermediate measurements). One-level step of Prove2Me ThresholdTheorem.level_k_concatenated_simulation.

import Mathlib
import Definitions.Def_threshold_theorem_local_stochastic

open ThresholdTheorem

namespace ThresholdTheorem
theorem level_one_local_stochastic_reduction :
    ∃ (c A : ℝ) (b : ℕ) (dec : (Fin b → Fin 2) → Fin 2), 1 ≤ c ∧
      ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (C : Circuit Q),
        ∃ C' : Circuit (Q × Fin b), (C'.size : ℝ) ≤ A * C.size ∧
          ∀ (e : ℝ), 0 ≤ e → ∀ P : (Q × Fin b → Fin 2) → ℝ, IsLocalStochasticDist C' e P →
            IsLocalStochasticDist C (c * e ^ 2) (pushDist (blockMap dec) P) := by sorry
end ThresholdTheorem
