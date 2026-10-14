-- Prove2me | Theorems.Thm_SourceTheory_EqualSources_pmatcher_identity
-- name    : SourceTheory.EqualSources.pmatcher_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:16.649178+00:00
-- url     : https://prove2.me/theorems/1f085f4e-a893-4a71-8d73-feb85ae28fa7
-- title:
--   Proof of Theorem 4, p. 8780 — a transformation linear on [0, 1/2] with φ(1/2) = 1/2 and φ(p) + φ(1 − p) = 1 is the identity on [0, 1]
-- statement:
--   Let $\varphi$ be a transformation (continuous, strictly increasing on $[0,1]$, mapping $[0,1]$ into itself, $\varphi(0) = 0$, $\varphi(1) = 1$). Suppose that for some constant $c$, $\varphi(p) = c\,p$ for all $p \in [0, \tfrac12]$, that $\varphi(\tfrac12) = \tfrac12$, and that $\varphi(p) + \varphi(1-p) = 1$ for all $p \in [0,1]$. Then
--
--   $$\varphi(p) = p \quad \text{for all } p \in [0,1].$$
--
--   In the proof of Theorem 4 this turns the pmatcher between two equally preferred and equally insensitive sources into the identity, which gives $w_{\mathcal A} = w_{\mathcal C}$.
-- source:
--   Baillon et al. (2025), Management Science 71(10), App. B, proof of Theorem 4, p. 8780

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

open Set

namespace SourceTheory.EqualSources

/-- Proof of Theorem 4, p. 8780: a transformation `φ` that is linear on `[0, 1/2]`, has
`φ(1/2) = 1/2` and satisfies `φ(p) + φ(1 − p) = 1` on `[0, 1]` is the identity on `[0, 1]`. -/
theorem pmatcher_identity (φ : ℝ → ℝ) (hφ : SourceTheory.Uniform.IsTransformation φ) (c : ℝ)
    (hlin : ∀ p ∈ Icc (0 : ℝ) (1 / 2), φ p = c * p) (hhalf : φ (1 / 2) = 1 / 2)
    (hsym : ∀ p ∈ Icc (0 : ℝ) 1, φ p + φ (1 - p) = 1) :
    ∀ p ∈ Icc (0 : ℝ) 1, φ p = p := by sorry

end SourceTheory.EqualSources
