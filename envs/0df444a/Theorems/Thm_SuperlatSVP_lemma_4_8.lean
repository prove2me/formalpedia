-- Prove2me | Theorems.Thm_SuperlatSVP_lemma_4_8
-- name    : SuperlatSVP.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:46:29.051388+00:00
-- url     : https://prove2.me/theorems/4869c9df-0d5e-4901-bd72-7fc30077b5e3
-- title:
--   Lemma 4.8 — pairs with a fixed difference, (4.18)–(4.20)
-- statement:
--   Let $\xi=e^{-n^{1/4}}$, let $H$ and $A$ be the target and midpoint shells of radius parameter $\lambda>0$, and for $z\in H$ let $E_z=\{x:x,\ x-z\in H,\ x-z/2\in A\}$. For a full-rank lattice $\Gamma$ put $K_{\Gamma,z}(u)=\#((\Gamma+u)\cap E_z)$, $K_\Gamma(u)=\#((\Gamma+u)\cap A)$ and $m_\Gamma=\operatorname{vol}(A)/\det\Gamma$, with $u$ uniform modulo $\Gamma$. For all sufficiently large $n$, uniformly in $\lambda$, $z,z'\in H$ and $\Gamma$:
--   $$(1-\xi)\operatorname{vol}(A)\le\operatorname{vol}(E_z)\le\operatorname{vol}(A),\tag{4.18}$$
--   $$(1-\xi)\,m_\Gamma\le\mathbb E_uK_{\Gamma,z}\le m_\Gamma,\tag{4.19}$$
--   and, if $\operatorname{Var}K_\Gamma\le\xi\,m_\Gamma^2$ (the standing assumption of p.36),
--   $$\mathbb E_u\big[K_{\Gamma,z}K_{\Gamma,z'}\big]\le(1+\xi)\,m_\Gamma^2.\tag{4.20}$$
--
--   The midpoint test therefore loses almost no pairs with a given difference, and the number of such pairs has controlled second moment. This is the single-merge estimate behind Lemmas 4.7 and 4.12.
--
--   **Formalization Note** One threshold $n_0$ is chosen before $\lambda$, $z$, $z'$ and $\Gamma$. The variance assumption is written $\mathbb EK_\Gamma^2\le(\mathbb EK_\Gamma)^2+\xi m_\Gamma^2$.
--
--   Differences from the source:
--   - generalization: the chain lattices Γ_j (0 ≤ j ≤ D) of the §4 setting (det L = 1, λ an estimate of λ1(L)) → every full-rank lattice Γ and every λ > 0; reason: the proof uses only the shells and the averaging identity (2.16); the chain lattices are instances
--   - encoding: "uniformly in z, z′ ∈ H and 0 ≤ j ≤ D" and Var K_Γ ≤ ξ m² → one n₀ before λ, z, z′, Γ, and E K² ≤ (E K)² + ξ m² in [0,∞]; reason: the means are finite; this is the source's uniformity
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §4.1.2, p.37 (PDF p.37), Lemma 4.8, eqs. (4.18)–(4.20); standing assumption p.36

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_SuperlatSVP_shellA
import Definitions.Def_SuperlatSVP_unifMean

open MeasureTheory Filter
open scoped ENNReal

namespace SuperlatSVP

/-- Lemma 4.8 (Pairs with a fixed difference). Hhan, Kim, Kim, Laarhoven, *Superlattice methods for the shortest vector problem and discrete
Gaussian sampling*, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §4.1.2, p.37 (PDF p.37): "Uniformly in
z, z′ ∈ H and 0 ≤ j ≤ D,
(1 − ξ) vol(A) ≤ vol(Ez) ≤ vol(A), (4.18)
(1 − ξ)mΓj ≤ EuKΓj,z ≤ mΓj, (4.19)
Eu[KΓj,z KΓj,z′] ≤ (1 + ξ)m²Γj, (4.20)
where u is uniform modulo Γj." Here `ξ = e^{−n^{1/4}}`, `E_z = {x : x, x − z ∈ H, x − z/2 ∈ A}`,
`K_{Γ,z}(u) = #((Γ + u) ∩ E_z)` (4.17), and (4.20) is under the standing assumption
"Var K_{Γj} ≤ ξm²_{Γj}" (p.36).

**Formalization Note.** Stated for every full-rank `Γ = B_Γℤⁿ` and every `λ > 0`, not only for the
chain lattices of §4 (the proof uses only these hypotheses); (4.20) carries the variance assumption
as a hypothesis, written `E K_Γ² ≤ (E K_Γ)² + ξm_Γ²`. "Uniformly" is one threshold `n₀` before
`λ, z, z′, Γ`. Volumes and means in `ℝ≥0∞`. -/
theorem lemma_4_8 :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ lam : ℝ, 0 < lam → ∀ z z' : E n, z ∈ shellH n lam →
      z' ∈ shellH n lam → ∀ BΓ : Matrix (Fin n) (Fin n) ℝ, BΓ.det ≠ 0 →
        (ENNReal.ofReal (1 - Real.exp (-((n : ℝ) ^ (1 / 4 : ℝ)))) * volume (shellA n lam) ≤
            volume (pairShell n lam z) ∧
          volume (pairShell n lam z) ≤ volume (shellA n lam)) ∧
        (ENNReal.ofReal (1 - Real.exp (-((n : ℝ) ^ (1 / 4 : ℝ)))) * shellMass n lam BΓ ≤
            unifMean BΓ (shiftCount (lat BΓ) (pairShell n lam z)) ∧
          unifMean BΓ (shiftCount (lat BΓ) (pairShell n lam z)) ≤ shellMass n lam BΓ) ∧
        (unifMean BΓ (fun u => shiftCount (lat BΓ) (shellA n lam) u ^ 2) ≤
            unifMean BΓ (shiftCount (lat BΓ) (shellA n lam)) ^ 2 +
              ENNReal.ofReal (Real.exp (-((n : ℝ) ^ (1 / 4 : ℝ)))) * shellMass n lam BΓ ^ 2 →
          unifMean BΓ (fun u => shiftCount (lat BΓ) (pairShell n lam z) u *
              shiftCount (lat BΓ) (pairShell n lam z') u) ≤
            ENNReal.ofReal (1 + Real.exp (-((n : ℝ) ^ (1 / 4 : ℝ)))) *
              shellMass n lam BΓ ^ 2) := by sorry

end SuperlatSVP
