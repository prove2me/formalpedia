-- Prove2me | Theorems.Thm_RegevLWE_Correctness_residue_law
-- name    : RegevLWE.Correctness.residue_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:07:42.450236+00:00
-- url     : https://prove2.me/theorems/83b8c09e-4647-4319-8989-c4111a4f11cd
-- title:
--   Proof of Lemma 5.1, p. 34:36 — for fixed S, Σ_{i∈S} e_i with e_i i.i.d. χ is distributed as χ^⋆|S|
-- statement:
--   Let $\chi$ be a probability distribution on $\mathbb Z_p$ and let $e_1, \dots, e_m \in \mathbb Z_p$ be chosen independently according to $\chi$. For every fixed subset $S \subseteq [m]$, the random variable $\sum_{i\in S} e_i$ (sum in $\mathbb Z_p$) has distribution
--   $$\sum_{i\in S} e_i \sim \chi^{\star |S|},$$
--   where $\chi^{\star k}$ is the distribution of the sum of $k$ independent samples from $\chi$ and $\chi^{\star 0}$ is the point mass at $0$.
--
--   Combined with the residue identity, this identifies the law of $b - \langle a, s\rangle$ for an encryption of $0$ under a fixed subset $S$.
--
--   **Formalization Note** The law of $(e_1,\dots,e_m)$ is the product `PMF` `iidPMF χ m`, and the statement is an equality of `PMF`s: the push-forward of `iidPMF χ m` under $e \mapsto \sum_{i\in S} e_i$ equals `convPow χ S.card`.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:36, proof of Lemma 5.1 ("The distribution of the latter is χ^⋆|S|.")

import Mathlib
import Definitions.Def_RegevLWE_Correctness_Cryptosystem

open Matrix

namespace RegevLWE.Correctness

/-- Proof of Lemma 5.1 (Regev, J. ACM 2009, p. 34:36): if `e₁, …, e_m ∈ ℤ_p` are chosen
independently according to `χ`, then for every fixed subset `S ⊆ [m]` the distribution of
`∑_{i∈S} eᵢ` is `χ^⋆|S|`. -/
theorem residue_law {p : ℕ} [NeZero p] {m : ℕ} (χ : PMF (ZMod p)) (S : Finset (Fin m)) :
    (iidPMF χ m).map (fun e => ∑ i ∈ S, e i) = convPow χ S.card := by sorry

end RegevLWE.Correctness
