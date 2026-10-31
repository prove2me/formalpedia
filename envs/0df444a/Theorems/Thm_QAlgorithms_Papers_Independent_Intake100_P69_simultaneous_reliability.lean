-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P69_simultaneous_reliability
-- name    : QAlgorithms.Papers.Independent.Intake100.P69.simultaneous_reliability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:28:06.631768+00:00
-- url     : https://prove2.me/theorems/c8d6adf3-93ea-487f-8dcd-f841fa4a4ee5
-- title:
--   Simultaneous teleportation is reliable for every sublinear input count
-- statement:
--   Let $k:\mathbb N\to\mathbb N$ satisfy $1\le k(N)\le N$ eventually and $k(N)/N\to0$. For each admissible $N$, Alice and Bob share $N$ normalized qubit singlets. There is a family of single joint POVMs, depending on $N$ and $k(N)$ but independent of the unknown input states, whose outcomes are ordered injections of the labeled inputs into the ports. Alice announces the injection once and Bob selects the corresponding halves in input order without correction.
--
--   For the resulting channels, measured in joint entanglement fidelity,
--
--   $$
--   \lim_{N\to\infty}F_{\rm e}(\mathcal P_{\rm sim}(N,k(N)))=1.
--   $$
--
--   The family is required to be a POVM at every admissible index. Inadmissible indices may be assigned arbitrary effect arrays; only finitely many occur and they do not affect the limit. This expresses the operational sublinear reliability claim without the undefined pointwise optimizer.
-- source:
--   Generalized teleportation and entanglement recycling, arXiv:1209.2683v2, PDF p. 4, Unnumbered sublinear simultaneous reliability, eq. (11)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P69

namespace QAlgorithms.Papers.Independent.Intake100.P69

open scoped ComplexConjugate

open Filter

/-- PDF p.4, prose following Theorem 2 and (11): every sublinear input count
admits an input-independent family of simultaneous measurements with limiting
joint entanglement fidelity one. At inadmissible finite indices no POVM is
required; reliability and admissibility are eventual properties. -/
theorem simultaneous_reliability (k : ℕ → ℕ)
    (hadmissible : ∀ᶠ N in atTop, 1 ≤ k N ∧ k N ≤ N)
    (hsmall : Tendsto (fun N => (k N : ℝ) / (N : ℝ)) atTop (nhds 0)) :
    ∃ M : (N : ℕ) → SimMeasurement N (k N),
      (∀ N, 1 ≤ k N → k N ≤ N → IsPOVM (M N)) ∧
      Tendsto (fun N => simultaneousFidelity (M N)) atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P69
