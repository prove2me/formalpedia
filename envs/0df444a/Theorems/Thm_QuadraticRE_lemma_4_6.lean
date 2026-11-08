-- Prove2me | Theorems.Thm_QuadraticRE_lemma_4_6
-- name    : QuadraticRE.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:11:21.117193+00:00
-- url     : https://prove2.me/theorems/f041ec13-6438-4590-93eb-0e487902960b
-- title:
--   Lemma 4.6 — a set of leaves reconstructs linearly or reveals nothing
-- statement:
--   Let $X\in\{A,C\}$, $j\ge0$ and $S\subseteq[L]$.
--
--   1. If $S$ is authorized for $\mathrm{Sh}^j_X$, there is an $\mathbb F_2$-linear map $\psi:\mathbb F_2^{S}\to\mathbb F_2$ with $\psi(\mathrm{Sh}^j_X(s;\theta)[S])=s$ for every root bit $s$ and every mask vector $\theta$.
--   2. If $S$ is unauthorized, then $\mathrm{Sh}^j_X(0;\theta)[S]$ and $\mathrm{Sh}^j_X(1;\theta)[S]$ have the same law over uniform masks $\theta$.
--
--   So the two recursive sharings are perfect: every set of shares either determines the root or carries no information about it.
--
--   Differences from the source:
--   - encoding: D ≡ D′ (statistical distance zero) → equality of the two laws as functions; reason: for laws, SD = 0 is equality
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Lemma 4.6, p.22

import Mathlib
import Definitions.Def_QuadraticRE_Auth

namespace QuadraticRE

/-- Lemma 4.6 of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), p.22: an authorized set has a linear reconstruction map, and an
unauthorized set has the same share law for the two root values. -/
theorem lemma_4_6 (X : Scheme) (j : ℕ) (S : Finset (Fin (4 ^ j))) :
    (Auth X j S → ∃ ψ : (S → F2) →ₗ[F2] F2,
      ∀ (s : F2) (θ : Fin (maskLen X j) → F2), ψ (S.restrict (Sh X j s θ)) = s) ∧
    (¬ Auth X j S →
      law (fun θ : Fin (maskLen X j) → F2 => S.restrict (Sh X j 0 θ))
        = law (fun θ : Fin (maskLen X j) → F2 => S.restrict (Sh X j 1 θ))) := by sorry

end QuadraticRE
