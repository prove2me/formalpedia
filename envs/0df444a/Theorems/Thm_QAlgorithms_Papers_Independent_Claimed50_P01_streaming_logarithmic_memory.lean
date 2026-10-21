-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P01_streaming_logarithmic_memory
-- name    : QAlgorithms.Papers.Independent.Claimed50.P01.streaming_logarithmic_memory
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:27:53.024751+00:00
-- url     : https://prove2.me/theorems/1b7e98c6-b440-4b3e-8adc-d583ab9f6baf
-- title:
--   Streaming weak Schur sampling with logarithmic quantum memory at fixed local dimension
-- statement:
--   Fix a local dimension $d\ge2$. The one-system Clebsch–Gordan operations can be chosen coherently, once for all stream lengths and input states, so that the sequential measured protocol performs weak Schur sampling on each fixed nonempty prefix. If $Q_\lambda^d$ is the unitary-group irreducible module indexed by the Young diagram $\lambda$, its peak active workspace after at most $n$ arrivals is
--
--   $$
--   m_d(n)=\max_{0\le k<n}\max_{\lambda\vdash_d k}\left\lceil\log_d\bigl(d\,\dim Q_\lambda^d\bigr)\right\rceil.
--   $$
--
--   There are constants $M_d>0$ and $N_d\ge2$, chosen before $n$ or the input state, such that
--
--   $$
--   \forall n\ge N_d,\qquad m_d(n)\le M_d\log_d n.
--   $$
--
--   For every fixed prefix length $k\ge1$, every unread length $r\ge0$, and every density operator $\rho$ on $(\mathbb C^d)^{\otimes(k+r)}$, write $\rho_{[k]}=\operatorname{Tr}_{\mathrm{unread}}\rho$. For every height-at-most-$d$ diagram $\lambda$ of size $k$, the probability that the sequential protocol reports $\lambda$ is $\operatorname{Tr}(\rho_{[k]}\Pi_\lambda^{\mathrm{Std}})$, where $\Pi_\lambda^{\mathrm{Std}}$ projects onto the full isotypic component. The workspace counts the retained irrep and the next arrival; classical history and unread systems outside the device are excluded.
--
--   This gives a streaming implementation on arbitrary, possibly mixed and entangled inputs. Termination is at a fixed prefix; no outcome-dependent stopping assertion is made. Constants may depend on $d$, and no quantitative dependence on a growing $d$ is asserted.
-- source:
--   Weak Schur sampling with logarithmic quantum memory, arXiv:2309.11947v1, PDF p. 1, Abstract; III and III.A

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P01

noncomputable section

open scoped Matrix

namespace QAlgorithms.Papers.Independent.Claimed50.P01

attribute [local instance] Classical.propDecidable

/-- Streaming weak Schur sampling with logarithmic active quantum memory for
each fixed d (PDF pp.1-2,6,10). Constants are before n and rho. The existential
CG family includes the required representation-theoretic existence, rather
than presupposing any dimension bound from the defective Eq.(48)-(49).
A fixed-prefix marginal is valid even for an entangled stream. -/
theorem streaming_logarithmic_memory (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : CGSystem d,
      (∃ M : ℝ, 0 < M ∧ ∃ N : ℕ, 2 ≤ N ∧
        ∀ n ≥ N, (peakMemory d n : ℝ) ≤ M * Real.logb d n) ∧
      (∀ (k : ℕ), 1 ≤ k → ∀ (r : ℕ)
        (rho : Matrix ((Fin (k + r) → Fin d)) ((Fin (k + r) → Fin d)) ℂ),
        IsDensityMatrix rho → ∀ lambda : Schur.Partition d k,
        labelProbability C lambda (prefixDensity k r rho) =
          effectProb (Schur.weakSampling d k lambda) (prefixDensity k r rho)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P01

end
