-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_lemma_3_6
-- name    : StochKolmogorov.Persist.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:32:16.476389+00:00
-- url     : https://prove2.me/theorems/0043324b-5c2d-4f34-8c4f-7acc15f20c54
-- title:
--   Lemma 3.6, p. 15 — for every T > 0 the skeleton chain (X(kT))_k on ℝⁿ,◦₊ is irreducible and aperiodic, and every compact K ⊂ ℝⁿ,◦₊ is petite
-- statement:
--   Throughout, $X$ is the solution of the stochastic Kolmogorov system $dX_i=X_if_i(X)\,dt+X_ig_i(X)\,dE_i$, $E=\Gamma^\top B$, $\Sigma=\Gamma^\top\Gamma=(\sigma_{ij})$, on $\mathbb R^n_+=[0,\infty)^n$ ($n\ge1$ populations), $\mathbb P_x,\mathbb E_x$ refer to the solution started at $x$, $\|x\|=\sum_i|x_i|$, and Assumption 1.1 (nondegenerate noise, locally Lipschitz coefficients, and the dissipativity condition (1.2) with $c\in\mathbb R^{n,\circ}_+$, $\gamma_b>0$) is in force.
--
--   For every $T>0$, the Markov chain $\{X(kT):k\in\mathbb N\}$ on $\mathbb R^{n,\circ}_+$ is irreducible and aperiodic. Moreover, every compact set $K\subset\mathbb R^{n,\circ}_+$ is petite.
--
--   Irreducibility, aperiodicity and petiteness of compact sets are the structural hypotheses of the Meyn–Tweedie theorem that, combined with the drift bound (4.18), yields the geometric ergodicity (4.26).
--
--   **Formalization Note** The $k$-step kernel of the skeleton chain is the transition probability at time $kT$. Irreducible, aperiodic and petite are as in the definition module (`SkelIrreducible`, `SkelAperiodic`, `SkelPetite`); aperiodicity is the Meyn–Tweedie notion (no cycle of $d\ge2$ nonempty disjoint sets), not the literal "smallest $d$" of p. 15, under which every chain is aperiodic. The process is a family `X x` of strong solutions of (1.1), one from each $x\in\mathbb R^n_+$, driven by one standard Brownian motion on one probability space (`IsSolutionFamily`); by pathwise uniqueness (Lemma 3.1) nothing depends on that choice. Coordinates are indexed by `Fin n` (0-based). $n\ge1$ is a standing hypothesis.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Lemma 3.6, p. 15

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Persist

open EthierKurtz

/-- Lemma 3.6 (p. 15): for every `T > 0` the skeleton chain `(X(kT))_{k ∈ ℕ}` on `ℝⁿ,◦₊` is
irreducible and aperiodic, and every compact `K ⊂ ℝⁿ,◦₊` is petite. -/
theorem lemma_3_6 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (T : ℝ≥0) (hT : 0 < T) :
    SkelIrreducible P X T ∧ SkelAperiodic P X T ∧
      ∀ K : Set (SDEState n), IsCompact K → K ⊆ openOrthant n → SkelPetite P X T K := by sorry

end StochKolmogorov.Persist
