-- Prove2me | Theorems.Thm_StationaryAction_maupertuis_lever_equilibrium
-- name    : StationaryAction.maupertuis_lever_equilibrium
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:43:31.532982+00:00
-- url     : https://prove2.me/theorems/2cff3da6-0d40-4eea-ae5e-e325dafa0844
-- title:
--   Maupertuis' lever: equilibrium from least action
-- statement:
--   Maupertuis' second application of his principle, §2.6 of the source: the balance point of a lever obtained by minimising an action.
--
--   Two bodies of masses $m_1 > 0$ and $m_2 > 0$ sit at the ends of a lever of length $L$, and $z$ denotes the distance from $m_1$ to the pivot. Under a small rotation the arcs described by the two bodies are proportional to $z$ and to $L - z$, so Maupertuis' quantity of action is proportional to
--
--   $$A(z) = m_1 z^2 + m_2 (L-z)^2 .$$
--
--   This is minimised at
--
--   $$z = \frac{m_2 L}{m_1 + m_2},$$
--
--   the classical equilibrium condition $m_1 z = m_2 (L - z)$ of the lever, as the source reports. The example matters historically because it is where Maupertuis claimed universality for his principle: the same rule that bends light also balances a beam.
--
--   **Formalization Note** The minimum is asserted over all real $z$, including values outside the physical range $[0, L]$; positivity of the masses is what makes $A$ convex and the stated point a genuine global minimiser.
-- source:
--   Julliana Rodrigues Martins, A Ação Estacionária como Eixo Unificador do Ensino de Física no Ensino Médio, Trabalho de Conclusão de Curso (Licenciatura em Física), Universidade Federal do Ceará, Fortaleza, 2025, 60 pp. §2.6, p. 30, lever example.

import Definitions.Def_StationaryActionCore

namespace StationaryAction

/-- Martins 2025, §2.6, Maupertuis' lever. -/
theorem maupertuis_lever_equilibrium
    (m₁ m₂ L : ℝ) (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    IsMinOn (fun z : ℝ => m₁ * z ^ 2 + m₂ * (L - z) ^ 2) Set.univ (m₂ * L / (m₁ + m₂)) := by
  sorry

end StationaryAction
