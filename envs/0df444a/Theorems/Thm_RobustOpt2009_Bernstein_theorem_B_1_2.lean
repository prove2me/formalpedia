-- Prove2me | Theorems.Thm_RobustOpt2009_Bernstein_theorem_B_1_2
-- name    : RobustOpt2009.Bernstein.theorem_B_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:42:30.947724+00:00
-- url     : https://prove2.me/theorems/a78273c0-7035-4418-b1a2-17123d0e08c2
-- title:
--   Theorem B.1.2 — robust representation of a closed homogenized level set
-- statement:
--   Let $\Psi:\mathbb R^n\to\mathbb R$ be convex and let $\psi:\mathbb R^m\to\mathbb R\cup\{+\infty\}$ be lower semicontinuous and convex with bounded real sublevel sets. Suppose
--   $$\Psi(z)=\sup_u\{\langle z,Bu+b\rangle-\psi(u)\}.$$
--   Let $\rho\in\mathbb R$ and $e\in\mathbb R^n$ satisfy $\rho<\Psi(0)$ and, for every $z$, $\lim_{t\to+\infty}\Psi(z+te)<\rho$. Define $Z^\rho_o=\{z:\exists\alpha>0,\ \Psi(\alpha z)\le\rho\}$ and $Z^\rho=\operatorname{cl} Z^\rho_o$. Then $U^\rho=\{u:\psi(u)\le-\rho\}$ is nonempty, convex, and compact, and
--   $$z\in Z^\rho\quad\Longleftrightarrow\quad\langle z,Bu+b\rangle\le0\quad\text{for every }u\in U^\rho.$$
--
--   This is the general dual representation used by the chapter's main result.
--
--   **Formalization Note** The directional limit is an extended-real limit and may equal $-\infty$, as it does in the chapter's application. The direction lies in the same space as $z$; the printed $\mathbb R^L$ is the surrounding notation for that space. The data structure uses names $\Phi,\phi,A,a$ for $\Psi,\psi,B,b$.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Theorem B.1.2, printed p. 473 (PDF p. 499)

import Definitions.Def_RobustOpt2009_Bernstein_Setup

open Set Filter Topology

namespace RobustOpt2009.Bernstein

theorem theorem_B_1_2 {n m : ℕ} (d : Setup n m) (ρ : ℝ) (e : Space n)
    (hPsi : ConvexOn ℝ univ d.Phi) (hQ2 : Q2 d)
    (hρ : ρ < d.Phi 0)
    (hlim : ∀ z, ∃ l : EReal, l < (ρ : EReal) ∧
      Tendsto (fun t : ℝ => (d.Phi (z + t • e) : EReal)) atTop (𝓝 l)) :
    (sublevel d.phi (-ρ)).Nonempty ∧ Convex ℝ (sublevel d.phi (-ρ)) ∧
    IsCompact (sublevel d.phi (-ρ)) ∧
    ∀ z, z ∈ dualCone d.Phi ρ ↔
      ∀ u ∈ sublevel d.phi (-ρ), pairing z (d.A u + d.a) ≤ 0 := by sorry

end RobustOpt2009.Bernstein
