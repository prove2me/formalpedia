-- Prove2me | Theorems.Thm_WalkTreeCluster_lemma_9_4
-- name    : WalkTreeCluster.lemma_9_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:03:22.484348+00:00
-- url     : https://prove2.me/theorems/6754708b-eb72-47d4-8e1a-ac655fceece9
-- title:
--   Lemma 9.4: for $u,v\in S\setminus B_{\rm clusters}$, the comparison stage window and the correctness of a trial
-- statement:
--   Let $G$ be an undirected $d$-regular graph ($d\ge1$) and $\mathcal C$ a family of clusters for $\epsilon,\phi$, with the parameters of Table 1, $0<\epsilon\le c_0\phi^2$ and $c_0$ defined from the constant $c_{\rm loc}$ of Lemma 8.3.
--   Fix distinct $u,v\in S\setminus B_{\rm clusters}$, write $C(z)$ for the cluster containing $z$ and $m=\min\{|C(u)|,|C(v)|\}$, and fix one depth-$h$ trial of Cluster$(u,v)$ whose returned values satisfy
--   $$\big|\langle F_i\mathbb 1_z,F_i\mathbb 1_{z'}\rangle_{w,h}-\langle F_i\mathbb 1_z,F_i\mathbb 1_{z'}\rangle_w\big|\le\frac{a^{20}}{\alpha^i}\qquad(z,z'\in\{u,v\},\ 1\le i\le h).$$
--   1. If $j\le h$ is the first stage at which the norm condition (120) holds, then
--   $$\frac{\alpha^j}{m}\ge\frac{a^{10}}{16\alpha},\qquad j>1\implies\frac{\alpha^j}{m}<a^{10}.$$
--   2. Whenever the trial tests the closeness of $u$ and $v$ (line 14), it sets $A_r=\textit{same}$ if $C(u)=C(v)$ and $\textit{different}$ otherwise. If the trial does not exceed its work cap and $h\ge h_*=\min\{k\ge1:\alpha^k\ge(a^{10}/\alpha)\,m\}$, it tests the closeness of $u$ and $v$ at a stage $j\le h_*$.
--
--   Differences from the source:
--   - encoding: an undirected d-regular graph G = (V, E) with self-loops counted once towards the degree, queried by (u, r) ↦ r-th neighbor → V = Fin n with neighbor lists nbr : Fin n → Fin d → Fin n (the r-th neighbor is nbr u (r − 1)), symmetric slot counts, at most one edge between distinct vertices, loops allowed; reason: Lean representation of the page's graph model (Section 4, Remark 4.1); same instances
--   - encoding: d-regular graph (d ≥ 1 implicit in M = (I + A/d)/2) → hypothesis 1 ≤ d; reason: the lazy walk matrix divides by d; Theorem 1.3 states d ≥ 1
--   - reading: q = 2000/a and t = 4000ϕ⁻² log(1/a) (Table 1) → q = ⌈2000/a⌉ and t = ⌈4000ϕ⁻² log(1/a)⌉; reason: q counts calls to Child and t counts walk steps, so both are integers; Table 1's α = q²/10⁶ ≤ 5a⁻² fits the rounded q
--   - encoding: the random variables X_{u,i}, Keep(u, i), X^keep_{u,i} produced by Algorithms 1–5 → their laws walkLaw, keepLaw, keepWalkLaw, defined by one measure recursion that follows Algorithms 1–5 step by step; reason: Lean works with laws; every law is proved to be a probability measure in the sanity files
--   - reading: c_loc is the absolute constant of Lemma 8.3 and c₀ = (1/8)min{10⁻⁴, (128c_loc)^{−1/60}}^{1000} (Table 1) → any c_loc for which the conclusion of Lemma 8.3 holds (LocalVariationConst c_loc), with ϵ ≤ c0Param(c_loc)·ϕ²; reason: Table 1 defines c₀ from the constant of Lemma 8.3; with lemma_8_3 (∃ c_loc) this is the page's statement
--   - encoding: one depth-h trial of Cluster(u, v) that does not exceed its work cap → the uncapped trial function trialOutcome / testStage of its estimates; reason: lines 8–18 of Algorithm 7 are a deterministic function of the returned values
--   - encoding: the values returned by the calls of one trial, each satisfying the accuracy bound → estimates at every stage 1 ≤ i ≤ h for all five calls, each within a²⁰/αⁱ; reason: the trial function never reads the other values, so imposing the bound on them as well changes nothing
--   - encoding: h* = min{…} → any h* that is the least element of the set (IsLeast); reason: the set is nonempty since α > 1; same instances
-- source:
--   Kapralov–Kochetkova, Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise, STOC 2027 submission (manuscript sha256 638eeef1…), Lemma 9.4, p.63

import Mathlib
import Definitions.Def_WalkTreeCluster_ExceptionalSets
import Definitions.Def_WalkTreeCluster_LocalVariationConst
import Definitions.Def_WalkTreeCluster_TrialDecision

namespace WalkTreeCluster

/-- **Lemma 9.4** (The comparison stage and correctness), p.63 (PDF p.66). Kapralov–Kochetkova,
*Sublinear Time Clustering: Taming Random Walks in Arbitrary Noise*, STOC 2027 submission
(manuscript sha256 638eeef1…).

Fix distinct `u, v ∈ S ∖ B_clusters` and one depth-`h` trial of `Cluster(u, v)` (Algorithm 7), with
values `⟨F_i1_z, F_i1_{z'}⟩_{w,h}` returned by its calls in lines 9 and 11–13, each within
`a^{20}/α^i` of `⟨F_i1_z, F_i1_{z'}⟩_w` (121). Write `C(z)` for the cluster of `z`.
(1) If `j ≤ h` is the first stage at which (120) holds, then
`α^j / min{|C(u)|, |C(v)|} ≥ a^{10}/(16α)`, and `j > 1 ⟹ α^j / min{|C(u)|, |C(v)|} < a^{10}`.
(2) Whenever Cluster tests the closeness of `u` and `v` (line 14), it sets `A_r = same` iff
`C(u) = C(v)`. If the trial does not exceed the work cap and
`h ≥ h_* = min{k ≥ 1 : α^k ≥ (a^{10}/α) min{|C(u)|, |C(v)|}}`, it tests at a stage `j ≤ h_*`.

**Formalization Note.** The trial is the uncapped trial function `trialOutcome` of its estimates;
the accuracy hypothesis is imposed on every estimate at every stage `1 ≤ i ≤ h` (values the trial
does not read are unused, so this is the same as imposing it on the returned values). `C(u), C(v)`
are the clusters `Cu ∋ u`, `Cv ∋ v` of the family. `h_*` is given by `IsLeast`. `c_loc` is a
constant for which the conclusion of Lemma 8.3 holds, and the parameters satisfy Table 1 with
`c₀ = c0Param c_loc`. -/
theorem lemma_9_4 (cloc : ℝ) (hcloc : LocalVariationConst cloc) {n d : ℕ}
    (nbr : Fin n → Fin d → Fin n) (ϵ ϕ : ℝ) (hd : 1 ≤ d) (hU : IsUndirected nbr)
    (hP : NoParallel nbr) (hϕ : 0 < ϕ) (hϕ1 : ϕ ≤ 1) (hϵ : 0 < ϵ)
    (hϵc : ϵ ≤ c0Param cloc * ϕ ^ 2) (𝒞 : Finset (Finset (Fin n)))
    (h𝒞 : IsClusterFamily nbr ϵ ϕ 𝒞) (u v : Fin n) (huv : u ≠ v)
    (Cu Cv : Finset (Fin n)) (hCu : Cu ∈ 𝒞) (hCv : Cv ∈ 𝒞) (hu : u ∈ Cu) (hv : v ∈ Cv)
    (huB : u ∉ Bclusters nbr ϵ ϕ 𝒞) (hvB : v ∉ Bclusters nbr ϵ ϕ 𝒞)
    (h : ℕ) (normEst : ℕ → Bool → ℝ) (uuEst vvEst uvEst : ℕ → ℝ)
    (hacc : ∀ i : ℕ, 1 ≤ i → i ≤ h →
      |normEst i false - wInner (aParam ϵ ϕ) (filter nbr ϵ ϕ i (coord u))
          (filter nbr ϵ ϕ i (coord u))| ≤ aParam ϵ ϕ ^ 20 / alphaParam ϵ ϕ ^ i ∧
      |normEst i true - wInner (aParam ϵ ϕ) (filter nbr ϵ ϕ i (coord v))
          (filter nbr ϵ ϕ i (coord v))| ≤ aParam ϵ ϕ ^ 20 / alphaParam ϵ ϕ ^ i ∧
      |uuEst i - wInner (aParam ϵ ϕ) (filter nbr ϵ ϕ i (coord u))
          (filter nbr ϵ ϕ i (coord u))| ≤ aParam ϵ ϕ ^ 20 / alphaParam ϵ ϕ ^ i ∧
      |vvEst i - wInner (aParam ϵ ϕ) (filter nbr ϵ ϕ i (coord v))
          (filter nbr ϵ ϕ i (coord v))| ≤ aParam ϵ ϕ ^ 20 / alphaParam ϵ ϕ ^ i ∧
      |uvEst i - wInner (aParam ϵ ϕ) (filter nbr ϵ ϕ i (coord u))
          (filter nbr ϵ ϕ i (coord v))| ≤ aParam ϵ ϕ ^ 20 / alphaParam ϵ ϕ ^ i) :
    (∀ j : ℕ, testStage ϵ ϕ h normEst = some j →
      aParam ϵ ϕ ^ 10 / (16 * alphaParam ϵ ϕ) ≤
          alphaParam ϵ ϕ ^ j / ((min Cu.card Cv.card : ℕ) : ℝ) ∧
      (1 < j → alphaParam ϵ ϕ ^ j / ((min Cu.card Cv.card : ℕ) : ℝ) < aParam ϵ ϕ ^ 10)) ∧
    (∀ (j : ℕ) (b : Bool), trialOutcome ϵ ϕ h normEst uuEst vvEst uvEst = some (j, b) →
      (b = true ↔ Cu = Cv)) ∧
    (∀ hstar : ℕ, IsLeast {k : ℕ | 1 ≤ k ∧
        aParam ϵ ϕ ^ 10 / alphaParam ϵ ϕ * ((min Cu.card Cv.card : ℕ) : ℝ) ≤
          alphaParam ϵ ϕ ^ k} hstar →
      hstar ≤ h → ∃ j ≤ hstar, testStage ϵ ϕ h normEst = some j) := by sorry

end WalkTreeCluster
