-- Prove2me | Theorems.Thm_PCSFBreach_Main_lemma_12
-- name    : PCSFBreach.Main.lemma_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:57:59.627115+00:00
-- url     : https://prove2.me/theorems/e2f9ff57-412d-468b-8408-4a2fe986f0bc
-- title:
--   Lemma 12 — gain is a nonnegative submodular function of collections of actively connected sets
-- statement:
--   Consider a run of the primal-dual algorithm with $\lambda=2$, $\mu=10^{-12}$ on a PCSF instance. On finite collections $\mathcal S$ of actively connected sets, $\mathrm{gain}(\mathcal S)=2\int_0^\infty(|A_t|-|A_t/\mathcal S|)\,dt$ takes values in $\mathbb R_{\ge 0}$ and is submodular: for all collections $\mathcal S_1,\mathcal S_2$ of actively connected sets,
--   $$\mathrm{gain}(\mathcal S_1\cup\mathcal S_2)+\mathrm{gain}(\mathcal S_1\cap\mathcal S_2)\le\mathrm{gain}(\mathcal S_1)+\mathrm{gain}(\mathcal S_2),\qquad \mathrm{gain}(\mathcal S)\ge 0 .$$
--
--   Submodularity is what allows a greedy choice of contractions in Lemma 6.
--
--   Differences from the source:
--   - generalization: an undirected graph G = (V, E) and a set D of pairs {s_i, t_i} → an edge list on the vertex set Fin n (parallel edges and loops allowed) and a pair list (repeated pairs and s_i = t_i allowed); reason: covers more instances: a simple graph with a set of distinct pairs is the case of lists without loops, parallel edges or repeats; a loop never lies in a forest and a pair with s_i = t_i is always connected
--   - encoding: the run of §4–§8 on a fresh instance (λ = 2, µ = 10^-12, p. 12) → every run with IsPDRun I 2 (1/10^12) R; reason: the section's standing parameters, kept as printed
--   - encoding: the run of the primal-dual algorithm (§2) → every record R : PDRun I with IsPDRun I λ μ R (event times 0 = t_0 < … < t_len, forests F_k, active moats A_k ⊇ normal-active moats N_k, obeying the §2 rules at every time); reason: the algorithm is continuous-time; moats and duals are determined by the instance and only the choice among simultaneously tight edges varies, so the statement is made for every run
--   - encoding: ∫_0^∞ … dt of a quantity of A_t → the finite sum over the stages [t_k, t_{k+1}) of the run of the stage length times the quantity; reason: A_t is constant on each stage and empty from the final time on, so the integral is that finite sum (no Bochner-integral junk values)
--   - encoding: submodular → f(𝒮₁ ∪ 𝒮₂) + f(𝒮₁ ∩ 𝒮₂) ≤ f(𝒮₁) + f(𝒮₂) on collections of actively connected sets (closed under ∪ and ∩); reason: the lattice definition, equivalent to the diminishing-returns form the proof checks
-- source:
--   Bosch-Calvo, Grandoni, Mátravölgyi, Breaching the 2-Approximation Barrier for Prize-Collecting Steiner Forest, STOC 2027 submission (manuscript sha256 05d9cc28…3eb3), p. 48, Lemma 12

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_PCSFBreach_Main_Instance
import Definitions.Def_PCSFBreach_Main_PrimalDual
import Definitions.Def_PCSFBreach_Main_ActiveConn
open QAlgorithms.Complexity

namespace PCSFBreach.Main

/-- Lemma 12 (p. 48): `gain`, on collections of actively connected sets, takes values in `ℝ≥0` and
is submodular. -/
theorem lemma_12 (I : Instance) (R : PDRun I) (hR : IsPDRun I 2 (1 / 10 ^ 12) R) :
    (∀ 𝒮 : Finset (Finset (Fin I.n)), R.IsActConnColl 𝒮 → 0 ≤ R.gain 𝒮) ∧
    ∀ 𝒮₁ 𝒮₂ : Finset (Finset (Fin I.n)), R.IsActConnColl 𝒮₁ → R.IsActConnColl 𝒮₂ →
      R.gain (𝒮₁ ∪ 𝒮₂) + R.gain (𝒮₁ ∩ 𝒮₂) ≤ R.gain 𝒮₁ + R.gain 𝒮₂ := by sorry

end PCSFBreach.Main
